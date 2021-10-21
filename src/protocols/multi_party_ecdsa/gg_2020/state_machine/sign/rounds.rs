#![allow(non_snake_case)]

use std::convert::TryFrom;
use std::iter;

use serde::{Deserialize, Serialize};
use thiserror::Error;

use curv::elliptic::curves::secp256_k1::{FE, GE};
use curv::BigInt;

use round_based::containers::push::Push;
use round_based::containers::{self, BroadcastMsgs, P2PMsgs, Store};
use round_based::Msg;

use crate::utilities::mta::{MessageA, MessageB};

use crate::protocols::multi_party_ecdsa::gg_2020 as gg20;
use crate::utilities::zk_pdl_with_slack::PDLwSlackProof;
use curv::cryptographic_primitives::proofs::sigma_correct_homomorphic_elgamal_enc::HomoELGamalProof;
use curv::cryptographic_primitives::proofs::sigma_valid_pedersen::PedersenProof;
use gg20::party_i::{
    LocalSignature, SignBroadcastPhase1, SignDecommitPhase1, SignKeys, SignatureRecid,
};
use gg20::state_machine::keygen::LocalKey;
use gg20::ErrorType;
use paillier::{Paillier, RawPlaintext, Decrypt, RawCiphertext, Randomness};
use curv::elliptic::curves::traits::*;
use curv::arithmetic::{Integer, BasicOps, Converter, Samplable};
use paillier::traits::Encrypt;
use std::ops::Mul;
use std::fs::File;
use std::io::{Write, BufReader, BufRead};
use std::borrow::Borrow;
use paillier::traits::EncryptWithChosenRandomness;

type Result<T, E = Error> = std::result::Result<T, E>;

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct GWI(pub GE);
#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct GammaI(pub MessageB);
#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct WI(pub MessageB);
#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct DeltaI(FE);
#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct TI(pub GE);
#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct TIProof(pub PedersenProof<GE>);
#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct RDash(GE);
#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct SI(pub GE);
#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct HEGProof(pub HomoELGamalProof<GE>);

pub struct Round0 {
    /// Index of this party
    ///
    /// Must be in range `[0; n)` where `n` is number of parties involved in signing.
    pub i: u16,

    /// List of parties' indexes from keygen protocol
    ///
    /// I.e. `s_l[i]` must be an index of party `i` that was used by this party in keygen protocol.
    // s_l.len()` equals to `n` (number of parties involved in signing)
    pub s_l: Vec<u16>,

    /// Party local secret share
    pub local_key: LocalKey,
}

impl Round0 {
    pub fn proceed<O>(self, mut output: O) -> Result<Round1>
    where
        O: Push<Msg<(MessageA, SignBroadcastPhase1)>>,
    {
        let mut sign_keys = SignKeys::create(
            &self.local_key.keys_linear.x_i,
            &self.local_key.vss_scheme.clone(),
            usize::from(self.s_l[usize::from(self.i - 1)]) - 1,
            &self
                .s_l
                .iter()
                .map(|&i| usize::from(i) - 1)
                .collect::<Vec<_>>(),
        );
        let (bc1, decom1) = sign_keys.phase1_broadcast();

        let party_ek = self.local_key.paillier_key_vec[usize::from(self.local_key.i - 1)].clone();
        let m_a = if self.i > 1 { MessageA::a(&sign_keys.k_i, &party_ek) }
        // malicious party encrypts large k_i value, chosen in a specific way
        else {
            let i = self.local_key.t as u32;
            let bad_k_1 = self.local_key.paillier_key_vec[0].n
                .div_floor(&FE::q()).mul(BigInt::from(2).pow(16*i + 1));
            sign_keys.k_i = ECScalar::from(&bad_k_1);
            let rand = BigInt::sample_below(&self.local_key.paillier_key_vec[0].n);
            let c_a = Paillier::encrypt_with_chosen_randomness(
                &self.local_key.paillier_key_vec[0],
                RawPlaintext::from(&bad_k_1),
                &Randomness::from(rand.clone()),
            );
            (MessageA { c: c_a.0.clone().into_owned() }, rand)
        };

        output.push(Msg {
            sender: self.i,
            receiver: None,
            body: (m_a.0.clone(), bc1.clone()),
        });

        let round1 = Round1 {
            i: self.i,
            s_l: self.s_l.clone(),
            local_key: self.local_key,
            m_a,
            sign_keys,
            phase1_com: bc1,
            phase1_decom: decom1,
        };

        Ok(round1)
    }

    pub fn is_expensive(&self) -> bool {
        true
    }
}

pub struct Round1 {
    i: u16,
    s_l: Vec<u16>,
    local_key: LocalKey,
    m_a: (MessageA, BigInt),
    sign_keys: SignKeys,
    phase1_com: SignBroadcastPhase1,
    phase1_decom: SignDecommitPhase1,
}

impl Round1 {
    pub fn proceed<O>(
        self,
        input: BroadcastMsgs<(MessageA, SignBroadcastPhase1)>,
        mut output: O,
    ) -> Result<Round2>
    where
        O: Push<Msg<(GammaI, WI)>>,
    {
        let (m_a_vec, bc_vec): (Vec<_>, Vec<_>) = input
            .into_vec_including_me((self.m_a.0.clone(), self.phase1_com.clone()))
            .into_iter()
            .unzip();

        let mut m_b_gamma_vec = Vec::new();
        let mut beta_vec = Vec::new();
        let mut m_b_w_vec = Vec::new();
        let mut ni_vec = Vec::new();

        let ttag = self.s_l.len();
        let l_s: Vec<_> = self
            .s_l
            .iter()
            .cloned()
            .map(|i| usize::from(i) - 1)
            .collect();
        let i = usize::from(self.i - 1);
        for j in 0..ttag - 1 {
            let ind = if j < i { j } else { j + 1 };
            let (m_b_gamma, beta_gamma, _beta_randomness, _beta_tag) = MessageB::b(
                &self.sign_keys.gamma_i,
                &self.local_key.paillier_key_vec[l_s[ind]],
                m_a_vec[ind].clone(),
            );
            let (m_b_w, beta_wi, _, _) = MessageB::b(
                &self.sign_keys.w_i,
                &self.local_key.paillier_key_vec[l_s[ind]],
                m_a_vec[ind].clone(),
            );

            m_b_gamma_vec.push(m_b_gamma);
            beta_vec.push(beta_gamma);
            m_b_w_vec.push(m_b_w);
            ni_vec.push(beta_wi);
        }

        let party_indices = (1..=self.s_l.len())
            .map(|j| u16::try_from(j).unwrap())
            .filter(|&j| j != self.i);
        for ((j, gamma_i), w_i) in party_indices.zip(m_b_gamma_vec).zip(m_b_w_vec) {
            output.push(Msg {
                sender: self.i,
                receiver: Some(j),
                body: (GammaI(gamma_i.clone()), WI(w_i.clone())),
            });
        }

        Ok(Round2 {
            i: self.i,
            s_l: self.s_l,
            local_key: self.local_key,
            sign_keys: self.sign_keys,
            m_a: self.m_a,
            beta_vec,
            ni_vec,
            bc_vec,
            m_a_vec,
            phase1_decom: self.phase1_decom,
        })
    }

    pub fn expects_messages(
        i: u16,
        n: u16,
    ) -> Store<BroadcastMsgs<(MessageA, SignBroadcastPhase1)>> {
        containers::BroadcastMsgsStore::new(i, n)
    }

    pub fn is_expensive(&self) -> bool {
        true
    }
}

pub struct Round2 {
    i: u16,
    s_l: Vec<u16>,
    local_key: LocalKey,
    sign_keys: SignKeys,
    m_a: (MessageA, BigInt),
    beta_vec: Vec<FE>,
    ni_vec: Vec<FE>,
    bc_vec: Vec<SignBroadcastPhase1>,
    m_a_vec: Vec<MessageA>,
    phase1_decom: SignDecommitPhase1,
}

impl Round2 {
    pub fn proceed<O>(self, input_p2p: P2PMsgs<(GammaI, WI)>, mut output: O) -> Result<Round3>
    where
        O: Push<Msg<(DeltaI, TI, TIProof)>>, // TODO: unify TI and TIProof
    {
        let (m_b_gamma_s, m_b_w_s): (Vec<_>, Vec<_>) = input_p2p
            .into_vec()
            .into_iter()
            .map(|(gamma_i, w_i)| (gamma_i.0, w_i.0))
            .unzip();

        let mut alpha_vec = Vec::new();
        let mut miu_vec = Vec::new();

        let ttag = self.s_l.len();
        let index = usize::from(self.i) - 1;
        let l_s: Vec<_> = self
            .s_l
            .iter()
            .cloned()
            .map(|i| usize::from(i) - 1)
            .collect();
        let g_w_vec = SignKeys::g_w_vec(
            &self.local_key.pk_vec[..],
            &l_s[..],
            &self.local_key.vss_scheme,
        );

        let mut output_ = None;
        // number of signature
        let i = self.local_key.t as u32;
        let g: GE = ECPoint::generator();
        let mut r = BigInt::from(0);
        let mut bad_k_i_fe: FE = FE::zero();
        let mut bad_k_i = BigInt::from(0);
        let mut G_j = vec![];
        let mut w_min = vec![];
        // we'll put parties' secrets in this vector
        let mut w_vec = vec![];
        // if we're the bad party, do stuff to prepare
        if self.i == 1 {
            bad_k_i = self.local_key.paillier_key_vec[0].n
                .div_floor(&FE::q()).mul(BigInt::from(2).pow(16*i + 1));
            r = self.local_key.paillier_key_vec[0].n
                .div_rem(&FE::q()).1;
            // precomputed values, list G in the paper
            G_j = (1..2_u32.pow(17) + 1).map(|k| {
                let r_j: BigInt = r.clone()*BigInt::from(k as u32);
                let r_j_fe: FE = ECScalar::from(&r_j);
                g * r_j_fe
            }).collect::<Vec<GE>>();
            bad_k_i_fe = ECScalar::from(&bad_k_i);
            // reading values that we saved after previous signatures
            let input = File::open("examples/tmp.txt").unwrap();
            let buffered = BufReader::new(input);
            for line in buffered.lines() {
                w_min.push(BigInt::from_hex(&line.unwrap()).unwrap());
            }
            output_ = Some(File::create("examples/tmp.txt").unwrap());
        }

        for j in 0..ttag - 1 {
            let ind = if j < index { j } else { j + 1 };
            let m_b = m_b_gamma_s[j].clone();

            let alpha_ij_gamma = if self.i > 1 {m_b
                .verify_proofs_get_alpha(&self.local_key.paillier_dk, &self.sign_keys.k_i)
                .expect("wrong dlog or m_b") }
            else {
                // the first signature we can even complete!
                if i == 1 {
                    let alice_share = Paillier::decrypt(&self.local_key.paillier_dk,
                                                    &RawCiphertext::from(&m_b.c));
                    let mut real_alpha: FE = ECScalar::from(&alice_share.0);
                    let g_alpha = g * real_alpha.clone();
                    let target_ge = m_b.b_proof.pk * bad_k_i_fe +
                        m_b.beta_tag_proof.pk.sub_point(&g_alpha.get_element());
                    for (k, &g_j) in G_j.iter().enumerate() {
                        if target_ge == g_j {
                            let j_bi_plus_one = BigInt::from(k as u32 + 1_u32);
                            let j_r: FE = ECScalar::from(&j_bi_plus_one.mul(&r));
                            real_alpha = real_alpha.add(&j_r.get_element());
                        }
                    }

                    let g_real_alpha = g * real_alpha;
                    assert_eq!(m_b.b_proof.pk * bad_k_i_fe + m_b.beta_tag_proof.pk, g_real_alpha);

                    // this is the actual value that malicious player will use
                    (real_alpha, real_alpha.to_big_int())
                }
                else {
                    (FE::zero(), BigInt::from(0))
                }
            };
            let m_b = m_b_w_s[j].clone();
            let alpha_ij_wi = if self.i > 1 { m_b
                .verify_proofs_get_alpha(&self.local_key.paillier_dk, &self.sign_keys.k_i)
                .expect("wrong dlog or m_b") }
            // malicious party does some processing here
            else {
                let alice_share = Paillier::decrypt(&self.local_key.paillier_dk,
                                                    &RawCiphertext::from(&m_b.c));
                let alpha: FE = ECScalar::from(&alice_share.0);
                let mut real_alpha: FE = alpha.clone();
                let g_alpha = g * alpha;
                let target_ge = m_b.b_proof.pk * bad_k_i_fe +
                    m_b.beta_tag_proof.pk.sub_point(&g_alpha.get_element());
                let two_pow = &BigInt::from(2_u32).pow(16*i+1);
                let target_ge_i = if i > 1 {
                    let s = (bad_k_i.clone().mul(w_min[j].clone())
                        .div_ceil(&self.local_key.paillier_key_vec[0].n)
                        .mul(&self.local_key.paillier_key_vec[0].n));
                    let sfe: FE = ECScalar::from(&s);
                    real_alpha = real_alpha.add(&sfe.get_element());
                    target_ge.sub_point(&(g * sfe).get_element())
                }
                else { target_ge.clone() };
                let mut w_i = FE::zero();

                // search over precomputed options
                for (k, &g_j) in G_j.iter().enumerate() {
                    if target_ge_i == g_j {
                        let j_bi = BigInt::from(k as u32);
                        let j_bi_plus_one = BigInt::from(k as u32 + 1_u32);
                        let mut q_j = if i > 1 { w_min[j].clone() + FE::q().mul(&j_bi).div_floor(two_pow) }
                            else { FE::q().mul(&j_bi).div_floor(two_pow) };
                        println!("Range to which party {}'s w_i was reduced by the attacker: [{:?}; {:?}]", j+2, q_j, q_j.add(&FE::q().div_floor(two_pow)));
                        let j_r: FE = ECScalar::from(&j_bi_plus_one.mul(&r));
                        real_alpha = real_alpha.add(&j_r.get_element());
                        // if it is the last iteration, do a quick search over the remaining options:
                        if i == 16_u32 {
                            w_i = loop {
                                let q_j_fe: FE = ECScalar::from(&q_j);
                                if g * q_j_fe == m_b.b_proof.pk {
                                    break q_j_fe
                                }
                                else { q_j = q_j.add(&BigInt::from(1)) }
                            }
                        }
                        let mut output__ = output_.as_ref().unwrap();
                        write!(output__, "{}", q_j.to_hex() + "\n").unwrap();
                    }
                }
                w_vec.push(w_i);

                // reconstructing a correct value in MtA only works for the first signature
                if i == 1 {
                    let g_real_alpha = g * real_alpha;
                    assert_eq!(m_b.b_proof.pk * bad_k_i_fe + m_b.beta_tag_proof.pk, g_real_alpha);
                }

                // this is the actual value malicious player was meant to receive
                (real_alpha, real_alpha.to_big_int())
            };
            assert_eq!(m_b.b_proof.pk, g_w_vec[ind]); //TODO: return error

            alpha_vec.push(alpha_ij_gamma.0);
            miu_vec.push(alpha_ij_wi.0);
        }
        if self.i == 1 {
            if i == 16
            {
                // recovered sk
                let secret_key = w_vec.iter().fold(self.sign_keys.w_i,
                                                   |acc, x|
                                                       acc.add(&x.get_element()));
                // check that it verifies
                assert_eq!(g * secret_key, self.local_key.public_key());
                println!("Secret key successfully recovered! It turns out to be: {}", secret_key.to_big_int());
            }
        }

        let delta_i = self.sign_keys.phase2_delta_i(&alpha_vec, &self.beta_vec);

        let sigma_i = self.sign_keys.phase2_sigma_i(&miu_vec, &self.ni_vec);
        let (t_i, l_i, t_i_proof) = SignKeys::phase3_compute_t_i(&sigma_i);
        output.push(Msg {
            sender: self.i,
            receiver: None,
            body: (DeltaI(delta_i), TI(t_i), TIProof(t_i_proof.clone())),
        });

        Ok(Round3 {
            i: self.i,
            s_l: self.s_l,
            local_key: self.local_key,
            sign_keys: self.sign_keys,
            m_a: self.m_a,
            mb_gamma_s: m_b_gamma_s,
            bc_vec: self.bc_vec,
            m_a_vec: self.m_a_vec,
            delta_i,
            t_i,
            l_i,
            sigma_i,
            t_i_proof,
            phase1_decom: self.phase1_decom,
        })
    }

    pub fn expects_messages(i: u16, n: u16) -> Store<P2PMsgs<(GammaI, WI)>> {
        containers::P2PMsgsStore::new(i, n)
    }

    pub fn is_expensive(&self) -> bool {
        true
    }
}

pub struct Round3 {
    i: u16,
    s_l: Vec<u16>,
    local_key: LocalKey,
    sign_keys: SignKeys,
    m_a: (MessageA, BigInt),
    mb_gamma_s: Vec<MessageB>,
    bc_vec: Vec<SignBroadcastPhase1>,
    m_a_vec: Vec<MessageA>,
    delta_i: FE,
    t_i: GE,
    l_i: FE,
    sigma_i: FE,
    t_i_proof: PedersenProof<GE>,

    phase1_decom: SignDecommitPhase1,
}

impl Round3 {
    pub fn proceed<O>(
        self,
        input: BroadcastMsgs<(DeltaI, TI, TIProof)>,
        mut output: O,
    ) -> Result<Round4>
    where
        O: Push<Msg<SignDecommitPhase1>>,
    {
        let (delta_vec, t_vec, t_proof_vec) = input
            .into_vec_including_me((DeltaI(self.delta_i), TI(self.t_i), TIProof(self.t_i_proof)))
            .into_iter()
            .map(|(delta_i, t_i, t_i_proof)| (delta_i.0, t_i.0, t_i_proof.0))
            .unzip3();

        let delta_inv = SignKeys::phase3_reconstruct_delta(&delta_vec);
        let ttag = self.s_l.len();
        for i in 0..ttag {
            PedersenProof::verify(&t_proof_vec[i]).expect("error T proof");
        }

        output.push(Msg {
            sender: self.i,
            receiver: None,
            body: self.phase1_decom.clone(),
        });

        Ok(Round4 {
            i: self.i,
            s_l: self.s_l,
            local_key: self.local_key,
            sign_keys: self.sign_keys,
            m_a: self.m_a,
            mb_gamma_s: self.mb_gamma_s,
            bc_vec: self.bc_vec,
            m_a_vec: self.m_a_vec,
            t_i: self.t_i,
            l_i: self.l_i,
            sigma_i: self.sigma_i,
            phase1_decom: self.phase1_decom,
            delta_inv,
            t_vec,
        })
    }

    pub fn expects_messages(i: u16, n: u16) -> Store<BroadcastMsgs<(DeltaI, TI, TIProof)>> {
        containers::BroadcastMsgsStore::new(i, n)
    }

    pub fn is_expensive(&self) -> bool {
        true
    }
}

pub struct Round4 {
    i: u16,
    s_l: Vec<u16>,
    local_key: LocalKey,
    sign_keys: SignKeys,
    m_a: (MessageA, BigInt),
    mb_gamma_s: Vec<MessageB>,
    bc_vec: Vec<SignBroadcastPhase1>,
    m_a_vec: Vec<MessageA>,
    t_i: GE,
    l_i: FE,
    sigma_i: FE,
    delta_inv: FE,
    t_vec: Vec<GE>,
    phase1_decom: SignDecommitPhase1,
}

impl Round4 {
    pub fn proceed<O>(
        self,
        decommit_round1: BroadcastMsgs<SignDecommitPhase1>,
        mut output: O,
    ) -> Result<Round5>
    where
        O: Push<Msg<(RDash, Vec<PDLwSlackProof>)>>,
    {
        let decom_vec: Vec<_> = decommit_round1.into_vec_including_me(self.phase1_decom.clone());

        let ttag = self.s_l.len();
        let b_proof_vec: Vec<_> = (0..ttag - 1).map(|i| &self.mb_gamma_s[i].b_proof).collect();
        let R = SignKeys::phase4(
            &self.delta_inv,
            &b_proof_vec[..],
            decom_vec.clone(),
            &self.bc_vec,
            usize::from(self.i - 1),
        )
        .expect(""); //TODO: propagate the error
        let R_dash = R * self.sign_keys.k_i;

        // each party sends first message to all other parties
        let mut phase5_proofs_vec = Vec::new();
        let l_s: Vec<_> = self
            .s_l
            .iter()
            .cloned()
            .map(|i| usize::from(i) - 1)
            .collect();
        let index = usize::from(self.i - 1);
        for j in 0..ttag - 1 {
            let ind = if j < index { j } else { j + 1 };
            let proof = LocalSignature::phase5_proof_pdl(
                &R_dash,
                &R,
                &self.m_a.0.c,
                &self.local_key.paillier_key_vec[l_s[index]],
                &self.sign_keys.k_i,
                &self.m_a.1,
                &self.local_key.h1_h2_n_tilde_vec[l_s[ind]],
            );

            phase5_proofs_vec.push(proof);
        }

        output.push(Msg {
            sender: self.i,
            receiver: None,
            body: (RDash(R_dash), phase5_proofs_vec.clone()),
        });

        Ok(Round5 {
            i: self.i,
            s_l: self.s_l,
            local_key: self.local_key,
            sign_keys: self.sign_keys,
            t_vec: self.t_vec,
            m_a_vec: self.m_a_vec,
            t_i: self.t_i,
            l_i: self.l_i,
            sigma_i: self.sigma_i,
            R,
            R_dash,
            phase5_proofs_vec,
        })
    }

    pub fn expects_messages(i: u16, n: u16) -> Store<BroadcastMsgs<SignDecommitPhase1>> {
        containers::BroadcastMsgsStore::new(i, n)
    }

    pub fn is_expensive(&self) -> bool {
        true
    }
}

pub struct Round5 {
    i: u16,
    s_l: Vec<u16>,
    local_key: LocalKey,
    sign_keys: SignKeys,
    t_vec: Vec<GE>,
    m_a_vec: Vec<MessageA>,
    t_i: GE,
    l_i: FE,
    sigma_i: FE,
    R: GE,
    R_dash: GE,
    phase5_proofs_vec: Vec<PDLwSlackProof>,
}

impl Round5 {
    pub fn proceed<O>(
        self,
        input: BroadcastMsgs<(RDash, Vec<PDLwSlackProof>)>,
        mut output: O,
    ) -> Result<Round6>
    where
        O: Push<Msg<(SI, HEGProof)>>,
    {
        let (r_dash_vec, pdl_proof_mat_inc_me): (Vec<_>, Vec<_>) = input
            .into_vec_including_me((RDash(self.R_dash), self.phase5_proofs_vec))
            .into_iter()
            .map(|(r_dash, pdl_proof)| (r_dash.0, pdl_proof))
            .unzip();

        let l_s: Vec<_> = self
            .s_l
            .iter()
            .cloned()
            .map(|i| usize::from(i) - 1)
            .collect();
        let ttag = self.s_l.len();
        for i in 0..ttag {
            LocalSignature::phase5_verify_pdl(
                &pdl_proof_mat_inc_me[i],
                &r_dash_vec[i],
                &self.R,
                &self.m_a_vec[i].c,
                &self.local_key.paillier_key_vec[l_s[i]],
                &self.local_key.h1_h2_n_tilde_vec,
                &l_s,
                i,
            ).map_err(|_| Error::Round6VerifyProof(ErrorType { error_type: "".to_string(), bad_actors: vec![] }));
        }
        LocalSignature::phase5_check_R_dash_sum(&r_dash_vec).map_err(|_| {
            Error::Round6VerifyProof(ErrorType { error_type: "R_dash".to_string(), bad_actors: vec![] })
        })?;

        let (S_i, homo_elgamal_proof) = LocalSignature::phase6_compute_S_i_and_proof_of_consistency(
            &self.R,
            &self.t_i,
            &self.sigma_i,
            &self.l_i,
        );

        output.push(Msg {
            sender: self.i,
            receiver: None,
            body: (SI(S_i.clone()), HEGProof(homo_elgamal_proof.clone())),
        });

        Ok(Round6 {
            S_i,
            homo_elgamal_proof,
            s_l: self.s_l,
            protocol_output: CompletedOfflineStage {
                i: self.i,
                local_key: self.local_key,
                sign_keys: self.sign_keys,
                t_vec: self.t_vec,
                R: self.R,
                sigma_i: self.sigma_i,
            },
        })
    }

    pub fn expects_messages(i: u16, n: u16) -> Store<BroadcastMsgs<(RDash, Vec<PDLwSlackProof>)>> {
        containers::BroadcastMsgsStore::new(i, n)
    }

    pub fn is_expensive(&self) -> bool {
        true
    }
}

pub struct Round6 {
    S_i: GE,
    homo_elgamal_proof: HomoELGamalProof<GE>,
    s_l: Vec<u16>,
    /// Round 6 guards protocol output until final checks are taken the place
    protocol_output: CompletedOfflineStage,
}

impl Round6 {
    pub fn proceed(
        self,
        input: BroadcastMsgs<(SI, HEGProof)>,
    ) -> Result<CompletedOfflineStage, Error> {
        let (S_i_vec, hegp_vec): (Vec<_>, Vec<_>) = input
            .into_vec_including_me((SI(self.S_i), HEGProof(self.homo_elgamal_proof)))
            .into_iter()
            .map(|(s_i, hegp_i)| (s_i.0, hegp_i.0))
            .unzip();
        let R_vec: Vec<_> = iter::repeat(self.protocol_output.R.clone())
            .take(self.s_l.len())
            .collect();

        LocalSignature::phase6_verify_proof(
            &S_i_vec,
            &hegp_vec,
            &R_vec,
            &self.protocol_output.t_vec,
        )
        .map_err(Error::Round6VerifyProof)?;
        LocalSignature::phase6_check_S_i_sum(&self.protocol_output.local_key.y_sum_s, &S_i_vec)
            .map_err(Error::Round6CheckSig)?;

        Ok(self.protocol_output)
    }

    pub fn expects_messages(i: u16, n: u16) -> Store<BroadcastMsgs<(SI, HEGProof)>> {
        containers::BroadcastMsgsStore::new(i, n)
    }

    pub fn is_expensive(&self) -> bool {
        true
    }
}

#[derive(Clone)]
pub struct CompletedOfflineStage {
    i: u16,
    local_key: LocalKey,
    sign_keys: SignKeys,
    t_vec: Vec<GE>,
    R: GE,
    sigma_i: FE,
}

impl CompletedOfflineStage {
    pub fn public_key(&self) -> &GE {
        &self.local_key.y_sum_s
    }
}

#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct PartialSignature(FE);

pub struct Round7 {
    local_signature: LocalSignature,
}

impl Round7 {
    pub fn new(
        message: &BigInt,
        completed_offline_stage: CompletedOfflineStage,
    ) -> Result<(Self, PartialSignature)> {
        let local_signature = LocalSignature::phase7_local_sig(
            &completed_offline_stage.sign_keys.k_i,
            &message,
            &completed_offline_stage.R,
            &completed_offline_stage.sigma_i,
            &completed_offline_stage.local_key.y_sum_s,
        );
        let partial = PartialSignature(local_signature.s_i.clone());
        Ok((Self { local_signature }, partial))
    }

    pub fn proceed_manual(self, sigs: &[PartialSignature]) -> Result<SignatureRecid> {
        let sigs = sigs.iter().map(|s_i| s_i.0).collect::<Vec<_>>();
        self.local_signature
            .output_signature(&sigs)
            .map_err(Error::Round7)
    }
}

#[derive(Debug, Error)]
pub enum Error {
    #[error("round 1: {0:?}")]
    Round1(ErrorType),
    #[error("round 2 stage 3: {0:?}")]
    Round2Stage3(crate::Error),
    #[error("round 2 stage 4: {0:?}")]
    Round2Stage4(ErrorType),
    #[error("round 3: {0:?}")]
    Round3(ErrorType),
    #[error("round 5: {0:?}")]
    Round5(ErrorType),
    #[error("round 6: verify proof: {0:?}")]
    Round6VerifyProof(ErrorType),
    #[error("round 6: check sig: {0:?}")]
    Round6CheckSig(crate::Error),
    #[error("round 7: {0:?}")]
    Round7(crate::Error),
}

trait IteratorExt: Iterator {
    fn unzip3<A, B, C>(self) -> (Vec<A>, Vec<B>, Vec<C>)
    where
        Self: Iterator<Item = (A, B, C)> + Sized,
    {
        let (mut a, mut b, mut c) = (vec![], vec![], vec![]);
        for (a_i, b_i, c_i) in self {
            a.push(a_i);
            b.push(b_i);
            c.push(c_i);
        }
        (a, b, c)
    }
}

impl<I> IteratorExt for I where I: Iterator {}
