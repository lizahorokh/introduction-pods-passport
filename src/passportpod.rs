pub mod parse;
use std::sync::LazyLock;

use anyhow::anyhow;
use itertools::Itertools;
use num::{bigint::BigUint, integer::div_ceil};
use plonky2::{
    field::types::Field,
    hash::{
        hash_types::{HashOut, HashOutTarget},
        hashing::hash_n_to_hash_no_pad,
        poseidon::{PoseidonHash, PoseidonPermutation},
    },
    iop::{
        target::{BoolTarget, Target},
        witness::{PartialWitness, WitnessWrite},
    },
    plonk::{
        circuit_builder::CircuitBuilder,
        circuit_data::{CircuitConfig, CircuitData, VerifierOnlyCircuitData},
        proof::{ProofWithPublicInputs, ProofWithPublicInputsTarget},
    },
};
use plonky2_ecdsa::{
    curve::{
        ecdsa::{ECDSAPublicKey, ECDSASignature},
        p256::P256,
    },
    gadgets::{
        biguint::{BigUintTarget, WitnessBigUint, convert_base},
        curve::CircuitBuilderCurve,
        ecdsa::{ECDSAPublicKeyTarget, ECDSASignatureTarget, verify_p256_message_circuit},
        nonnative::{BITS, CircuitBuilderNonNative},
    },
};
use plonky2_sha256::circuit::{
    VariableLengthSha256Targets, fill_variable_length_circuits, make_variable_length_circuits,
};
use plonky2_ux::gadgets::arithmetic_ux::UXTarget;
use pod2::{
    backends::plonky2::{
        Error, Result,
        basetypes::{C, D, Proof},
        circuits::{
            common::{
                CircuitBuilderPod, Flattenable, StatementArgTarget, StatementTarget, ValueTarget,
            },
            mainpod::CalculateIdGadget,
        },
        deserialize_proof,
        mainpod::{self, calculate_id, get_common_data},
        serialize_proof,
    },
    measure_gates_begin, measure_gates_end,
    middleware::{
        self, AnchoredKey, BackendError, F, Hash, KEY_TYPE, Key, NativePredicate, Params, Pod,
        PodId, RawValue, RecursivePod, SELF, Statement, ToFields, TypedValue, VALUE_SIZE, VDSet,
        Value,
    },
    timed,
};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::{
    gadgets::{
        bits_bytes::bits_to_bytes_be,
        comparison::check_less_or_equal,
        search::{merkle_root_rabin_karp_circuit, merkle_tree, LookupTarget},
    }, mdlpod::parse::{parse_data, sha_256_pad, DataType, EntryTarget, MdlData}, passportpod::parse::PassportEntryTarget, PodType
};

pub const PASSPORT_ENTRIES : [&str; 9] = [
        "data_type",
        "issuing_state",
        "surname",
        "name",
        "document_number",
        "nationality",
        "birth_date",
        "sex",
        "expiration_date"];

pub fn data_info(flag: &str) -> (usize, usize){
    //returns tuple (data_offset, data_max_size)
    match flag {
        "dg1" => (75 as usize, 93 as usize),
        "eContent" => (72 as usize, 336 as usize),
        "signAttr" => (240 as usize, 208 as usize)
    }
}

///connects dg1 data in passport entry to the hash of dg1 data (original message)
fn connect_passport_entry_and_hash(
    builder: &mut CircuitBuilder<F, D>,
    entry: &PassportEntryTarget,
    hash: &VariableLengthSha256Targets,
) {
    let hash_msg_bytes = bits_to_bytes_be(builder, &hash.message);
    builder.connect_slice(&hash_msg_bytes, &entry.dg1[..]);
    let bytes_per_block = builder.constant(F::from_canonical_u32(32));
    let max_allowed_end = builder.mul(bytes_per_block, hash.msg_blocks.0);
    check_less_or_equal(
        builder,
        entry.end_index,
        max_allowed_end,
        (hash.message.len().ilog2() - 2) as usize,
    );
}


//give a string of characters and hash, connects hash to its apperance in the string
pub fn connect_hash_inside_message(builder: &mut CircuitBuilder<F, D>, hash: VariableLengthSha256Targets, message: Vec<BoolTarget>, hash_offset: usize){
    //let hash_bytes = bits_to_bytes_be(builder, &hash.digest);
    builder.connect_slice(&message[hash_offset .. hash_offset + 256], &hash.digest);
}


//proves the entries are in dg1 content. hash(dg1) -> in eContent, hash(eContent) -> in signAttr
struct PassportDocTarget{
    entries: Vec<PassportEntryTarget>, 
    dg1: VariableLengthSha256Targets,
    eContent: VariableLengthSha256Targets,
    signAttr: Vec<BoolTarget>, 
}

//for now, assumes that the position of the hashes is fixed, but might not be true
//general passport structure is that all main information is stored in dg1 section, then dg1 data is hashed
//all dg groups are hashed together to form eContent
//eContent is hashed and padded with scheme information to create signAttr
//signature (RSA 4096) signs the padded hash of signAttr (sometimes called encapContent)
struct PassportData{
    signature: Vec<u8>,
    pk: Vec<u8>,
    signAttr: Vec<u8>,
    dg1: Vec<u8>,
    eContent: Vec<u8>
}



impl PassportDocTarget{
    pub fn add_targets(builder: &mut CircuitBuilder<F, D>, passport_fields : Vec<&str>){
        //let dg1 = builder.add_virtual_targets(data_info("dg1")[1]);
        //let eContent = builder.add_virtual_targets(data_info("eContent")[1]);
        let entries: Vec<PassportEntryTarget> = Vec::new();
        let signAttr = builder.add_bool_virtual_targets(data_info("signAttr")[1] * 8);
        let hash_dg1 =
                plonky2_sha256::circuit::make_variable_length_circuits(builder, data_info("dg1")[1] * 8);
        let hash_eContent =
                plonky2_sha256::circuit::make_variable_length_circuits(builder, data_info("eContent")[1] * 8);    
        connect_hash_inside_message(builder, hash_dg1, hash_eContent.message, data_info("dg1")[0] * 8);
        connect_hash_inside_message(builder, hash_eContent, signAttr, data_info("eContent")[0] * 8);
        for field in passport_fields{
            let entry = PassportEntryTarget::new(builder, field);
            connect_passport_entry_and_hash(builder, entry, hash_dg1);
            entries.push(entry);
        }
        measure_gates_end!(builder, measure);
        
        PassportDocTarget {
            entries,
            dg1: hash_dg1,
            eContent: hash_eContent,
            signAttr
        }
    }
    pub fn set_targets(&self, pw: &mut PartialWitness<F>, data: &PasportData) -> anyhow::Result<()> {
        //let mut eContent_padded = data.eContent.clone();
        //sha_256_pad(&mut eContent_padded, MSO_MAX_BLOCKS)?;
        assert!(data.dg1.len() == data_info("dg1")[1]);
        assert!(data.eContent.len() == data_info("eContent")[1]);
        assert!(data.signAttr.len() == data_info("signAttr")[1]);

        let sign_attr_bits : Vec<u8> = Vec::new();

        for byte in data.signAttr {
            for _ in 0 .. 8{
                sign_attr_bits.push(byte % 2);
                byte = byte / 2;
            }
        }

        for (&ch_t, &ch) in self.signAttr.iter().zip(sign_attr_bits.iter()) {
            pw.set_target(ch_t, F::from_canonical_u8(ch))?;
        }
        fill_variable_length_circuits::<_, 2>(
                pw,
                &data.dg1,
                data_info("dg1")[1] * 8,
                &self.dg1,
            )?;
        
        fill_variable_length_circuits::<_, 2>(
                pw,
                &data.eContent,
                data_info("eContent")[1]* 8,
                &self.eContent,
            )?;
        Ok(())
    }

}

pub struct RSADecryptTarget{
    pk: Vec<BigUintTarget<27>>,
    signature: Vec<BigUintTarget<27>>,
    message: Vec<BigUintTarget<27>>,
}

/// Builds the RSA part of the circuit.  Returns the message that was signed in signature
pub fn build_rsa(builder: &mut CircuitBuilder<F, D>) -> RSADecryptTarget {
    let signature = builder.add_virtual_biguint_target(RSA_LIMBS);
    let modulus = builder.add_virtual_biguint_target(RSA_LIMBS);
    let computed_padded_data = pow_65537(builder, &signature, &modulus);
    RSADecryptTarget {
        pk: modulus,
        signature,
        message: computed_padded_data,
    }
}

impl RSADecryptTarget{
    fn add_targets(builder: &mut CircuitBuilder<F, D>, number_bytes: usize){
        
    }
    fn set_targets(builder: &mut CircuitBuilder<F, D>, number_bytes: usize){
        
    }
}
pub struct PassportVerifyTarget {
    doc: PassportDocTarget,
    sig: RSADecryptTarget,
}

impl PassportVerifyTarget {
    fn add_targets(builder: &mut CircuitBuilder<F, D>) -> Self {
        let sig = RSADecryptTarget::add_targets(builder, 4096);
        let doc = PassportDocTarget::add_targets(builder, PASSPORT_FIELDS);

        let sign_attr_hash = make_variable_length_circuits(builder, RSA_SIZE * 8);
        builder.connect_slice(sign_attr_hash.message, doc.signAttr);

        let number_limbs = sig.message.limbs.len();
        let mut last_bits : Vec<BoolTarget> = Vec::new();
        for i in 0 as usize .. 10 as usize{
            let mut limb_bits = builder.split_le(sig.message.limbs[i].0, 27);
            last_bits.append(&limb_bits);
        }
        builder.connect_slice(sign_attr_hash.digest, last_bits[0..256]);
        //connect_doc_and_hash(builder, &doc, &sig.sha256_targets);
        Self { doc, sig }
    }

    pub fn set_targets(
        &self,
        pw: &mut PartialWitness<F>,
        passport_data: &MdlData,
    ) -> anyhow::Result<()> {
        self.doc.set_targets(pw, passport_data)?;
        self.sig
            .set_targets(pw, passport_data.signature.clone(), *ppassport_data.pk.clone())?;
        Ok(())
    }
}
