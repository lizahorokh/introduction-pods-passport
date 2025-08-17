use anyhow::Result;   
use pod2::backends::plonky2::circuits::utils::DebugGenerator;                
use plonky2::util::serialization::{Read, Write};     
use plonky2::hash::hash_types::RichField;
use plonky2::field::extension::Extendable; 
use std::marker::PhantomData;
use plonky2::plonk::circuit_data::CommonCircuitData;
use plonky2::util::serialization::IoResult;
use std::ops::Range;
use anyhow::anyhow;
use ciborium::{Value, from_reader, into_writer};
use itertools::Itertools;
use num::BigUint;
use plonky2::{
    field::types::Field,
    iop::{
        target::{BoolTarget, Target},
        witness::{PartialWitness, WitnessWrite, PartitionWitness, Witness},
        generator::{SimpleGenerator, GeneratedValues}
    },
    plonk::circuit_builder::CircuitBuilder,
};
use plonky2_ecdsa::{
    curve::{ecdsa::ECDSASignature, p256::P256},
    field::p256_scalar::P256Scalar,
};
use pod2::{
    backends::plonky2::{
        basetypes::{D, F},
        circuits::common::ValueTarget,
    },
    middleware::{TypedValue, hash_str},
};
use serde::Deserialize;

use crate::gadgets::{hash_var_len::pod_str_hash, shift::shift_left};

#[derive(Debug)]
pub struct PassportEntryTarget {
    pub dg1: Box<[Target; 93]>, //whole dg1 data, sequence of 93 utf8_string
    pub start_index: Target, //offset of the start of the data inside dg1 string
    pub end_index: Target, // index of the end of the data, without padding 
    pub value: ValueTarget, //extracted data
    pub field_name: String, //name of the entry
}
//list of all data that is stored in dg1 section of passport
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


//returns the index of slice where appears field_name in the dg1 data. Assumes 5 bytes prefix.
pub fn index_field_name(field_name : &str) -> Range<usize> {
    match field_name{
        "data_type" => 5..7,
        "issuing_state" => 7..10,
        "surname" =>  10..49,
        "name" =>  10..49,
        "document_number" => 49..58,
        "nationality" => 59..62,
        "birth_date" => 62..68,
        "sex" => 69..70,
        "expiration_date" =>  70..76,
        _ => 0..0,
    }
}



//in passport's dg1 data, there is fixed number of characters per field, so if there is extra space, it is filled with "<"
fn length_without_padding(builder: &mut CircuitBuilder<F, D>, utf8_string: &[Target], max_length: Target) -> Target {
    //given the string of utf8 symbols (max length), returns new length without "<" padding
    //(proven inside the circuit)
    
    let mut current_length = max_length;
    let mut padding_symbol = builder.constant(F::from_canonical_u8(60u8));
    let one =  builder.constant(F::from_canonical_u8(1u8));
    let zero =  builder.constant(F::from_canonical_u8(0u8));
    for symbol in utf8_string{
        let is_padded = builder.is_equal(padding_symbol, *symbol);
        let is_padded_bit =  builder._if(is_padded, one, zero);
        current_length = builder.sub(current_length, is_padded_bit);
    }
    current_length
}



struct RangeTarget{
    start: Target,
    length: Target,
}


fn parse_full_name(builder: &mut CircuitBuilder<F, D>, utf8_string: &[Target], field_name: &str) -> RangeTarget {
    //in the dg1 full name represented as surname1<surname2..<<name1<name2..., 
    //where different parts of name and surname are separated with "<"
    //and the whole string is padded with "<" to be the correct length
    //this function generates index for the start of name or surname(based on field_name) and its length
    // and then checks that it actually separates name and surname
    // and * TODO * changes "<" to " " to support multiple names
    assert!(field_name == "name" || field_name == "surname");
    let mut end_surname_index = builder.add_virtual_target();
    builder.add_simple_generator(SurnameSeparatorGenerator::<F, D> {
        data : utf8_string.clone().to_vec(),
        end_surname_index : end_surname_index,
        _phantom: PhantomData,
    });
   
    let full_length = builder.constant(F::from_canonical_usize(utf8_string.len()));
    let zero = builder.constant(F::from_canonical_u8(0));
    let one = builder.constant(F::from_canonical_u8(1));
    let three = builder.constant(F::from_canonical_u8(3));
    
    let padding_symbol = builder.constant(F::from_canonical_u8(60));
    //checks that end_surname_index actually separates name and surname
        let bits_end_surname_index : Vec<BoolTarget> = builder.split_le_base::<2>(end_surname_index, 5).into_iter().map(BoolTarget::new_unsafe).collect();
        let shifted_name = shift_left(builder, utf8_string.as_ref(), &bits_end_surname_index);
        let check_0 = builder.is_equal(padding_symbol, shifted_name[0]);
        let check_1 = builder.is_equal(padding_symbol, shifted_name[1]);
        let check_2 = builder.is_equal(padding_symbol, shifted_name[2]);
        let check_3 = builder.is_equal(padding_symbol, shifted_name[3]);
        let check_0_bit = builder._if(check_0, one, zero);
        let check_1_bit = builder._if(check_1, one, zero);
        let check_2_bit = builder._if(check_2, one, zero);
        let check_3_bit = builder._if(check_3, one, zero);
        builder.connect(zero, check_0_bit);
        builder.connect(one, check_1_bit);
        builder.connect(one, check_2_bit);
        builder.connect(zero, check_3_bit);
    //* TODO * actual_name changes all "<" symbols to " " in original string (in case person has multiple surnames)
    //creates a constant of utf8 index of " "
    //let space = builder.constant(F::from_canonical_u8(32));
    //let actual_surname = utf8_string.map(|symbol| builder._if(builder.is_equal(padding_symbol, symbol), space, symbol));
    if field_name == "surname"{
        let surname_length = builder.add(end_surname_index, one);
        return RangeTarget{
            start : zero,
            length : surname_length,
        };
    }
    let start_name_index = builder.add(three, end_surname_index);
    let name_length_assumption = builder.sub(full_length, start_name_index);
    let bits_start_index : Vec<BoolTarget> = builder.split_le_base::<2>(start_name_index, 5).into_iter().map(BoolTarget::new_unsafe).collect();
    let name_string = shift_left(builder, utf8_string.as_ref(), &bits_start_index);
    
    let name_length = length_without_padding(builder, &name_string, name_length_assumption);
    
    RangeTarget{
        start: start_name_index,
        length: name_length,
    }
}

#[derive(Debug)]
struct SurnameSeparatorGenerator<F: RichField + Extendable<D>, const D: usize> {
    //should generate an index at which surname ends
    data: Vec<Target>,
    end_surname_index: Target,
    _phantom: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize> SimpleGenerator<F, D>
    for SurnameSeparatorGenerator<F, D>
{
    fn id(&self) -> String {
        "SurnameSeparatorGenerator".into()
    }

    fn dependencies(&self) -> Vec<Target> {
        self.data.to_vec()
    }

    fn run_once(
        &self,
        witness: &PartitionWitness<F>,
        out_buffer: &mut GeneratedValues<F>,
    ) -> Result<()> {
        //looks for the first "<" symbol, *TODO* look for first "<<" in case of multiple names
        let utf8_string : Vec<_> = self.data.clone().into_iter().map(|symbol| witness.get_target(symbol)).collect();
        let mut result = 0;
        //assumes that person has only one surname and looks for the first padding symbol
        while utf8_string[result] != F::from_canonical_u8(60) {
            result += 1;
        }
        println!("result is: {result}");
        out_buffer.set_target(self.end_surname_index, F::from_canonical_u8(result as u8 - 1));
        Ok(())
    }

    fn serialize(&self, dst: &mut Vec<u8>, _common_data: &CommonCircuitData<F, D>) -> IoResult<()> {
        dst.write_target_vec(&self.data)?;
        dst.write_target(self.end_surname_index)
    }

    fn deserialize(
        src: &mut plonky2::util::serialization::Buffer,
        _common_data: &CommonCircuitData<F, D>,
    ) -> IoResult<Self>
    where
        Self: Sized,
    {
        let data = &src.read_target_vec()?;
        let end_surname_index =&src.read_target()?;

        Ok(Self {
            data: data.clone(),
            end_surname_index: *end_surname_index,
            _phantom: PhantomData,
        })
    }
}


impl PassportEntryTarget {
    pub fn new(builder: &mut CircuitBuilder<F, D>, field_name: &str) -> Self {
        // don't need to range check dg1 here, because it gets range checked
        // when it's converted to utf8_string for the SHA256 hash
        //gets the default range for the entry
        let range: Range<usize>  = index_field_name(field_name);
        let dg1 : Box<[Target; 93]> = Box::new(core::array::from_fn(|_| builder.add_virtual_target()));
        let slice: Vec<Target> = dg1[range.clone()].to_vec();
        //will store future results
        let entry : ValueTarget;
        let start_index : Target;
        let entry_length : Target;
        
        if (field_name == "name") || (field_name == "surname")
        {
            let full_name_start = builder.constant(F::from_canonical_u8(range.start as u8));
            let range_field = parse_full_name(builder, &slice, field_name);
            start_index = builder.add(range_field.start, full_name_start);
            entry_length = range_field.length;

            entry = match field_name{
                "surname" => ValueTarget {
                    elements: pod_str_hash(builder, &slice, entry_length).elements,
                    },
                _ => {
                    let bits_start_index : Vec<BoolTarget> = builder.split_le_base::<2>(range_field.start, 5).into_iter().map(BoolTarget::new_unsafe).collect();
                    let name_string = shift_left(builder, slice.as_ref(), &bits_start_index);
                    ValueTarget {
                    elements: pod_str_hash(builder, &name_string, entry_length).elements,
                    }
                }
            } 
        } else {
            let entry_length_max = builder.constant(F::from_canonical_u8(range.end as u8 - range.start as u8));
            entry_length = length_without_padding(builder, &slice, entry_length_max);
            entry = ValueTarget {
                elements: pod_str_hash(builder, &slice, entry_length).elements,
            };
            start_index = builder.constant(F::from_canonical_u8(range.start as u8)); 
        }
        let end_index = builder.add(start_index, entry_length);
        println!("field name: {:?}", field_name);
        builder.add_simple_generator(DebugGenerator::new(
            format!("resulting entry"),
            entry.elements.to_vec(),
        ));
        builder.add_simple_generator(DebugGenerator::new(
            format!("indexes and length: "),
            [start_index, end_index, entry_length].to_vec(),
        ));
        
        
        Self {
            dg1: dg1,
            start_index: start_index,
            end_index: end_index,
            value: entry,
            field_name: field_name.to_string(),
        }

    }

    pub fn set_targets(&self, pw: &mut PartialWitness<F>, dg1: &[u8]) -> anyhow::Result<()> {
        assert!(dg1.len() == 93);

        for (&symbol_t, symbol) in self.dg1.iter().zip_eq(dg1.into_iter()) {
            pw.set_target(symbol_t, F::from_canonical_u8(*symbol))?;
        }
        Ok(())
    }
}

#[cfg(test)]
pub(crate) mod test {
    use super::PassportEntryTarget;   
    use anyhow::anyhow;
    use sha2::{Sha256, Digest};

    use plonky2::{
        iop::witness::{PartialWitness, WitnessWrite, PartitionWitness, Witness},
        
        plonk::{
            circuit_builder::CircuitBuilder, circuit_data::CircuitConfig,
            config::PoseidonGoldilocksConfig,
        },
    };
    use pod2::backends::plonky2::circuits::utils::DebugGenerator;
    use crate::{mdlpod::parse::{DataType, EntryTarget, MdlData}, passportpod::rawPassportEntries};

    const DG1_DATA: [u8; 93] = [
        97, 91, 95, 31, 88, 80, 60, 85, 75, 82, 72, 79, 82, 79, 75, 72, 60, 60, 89, 69, 76, 89, 90, 65,
        86, 69, 84, 65, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60,
        60, 70, 90, 57, 56, 57, 57, 49, 51, 60, 55, 85, 75, 82, 48, 53, 48, 55, 48, 51, 55, 70, 50, 53,
        48, 51, 49, 49, 52, 50, 48, 48, 53, 48, 55, 48, 51, 48, 49, 49, 54, 49, 60, 56, 52,
    ];

    

    //pub fn cbor_parsed() -> anyhow::Result<MdlData> {
    //    parse_data(CBOR_DATA)
    //}

    /*#[test]
    fn test_parse() -> anyhow::Result<()> {
        parse_data(CBOR_DATA)?;
        Ok(())
    }*/

    #[test]
    fn test_parsing_data() -> anyhow::Result<()> {
        let mut hasher = Sha256::new();
        hasher.update(DG1_DATA);
        let hash_dg1 = hasher.finalize();

        println!("The hash of dg1 data: {:?}", hash_dg1);
        for field_name in rawPassportEntries {
            let mut builder = CircuitBuilder::new(CircuitConfig::standard_recursion_config());
            let entry_t = PassportEntryTarget::new(&mut builder, field_name);
            let data = builder.build::<PoseidonGoldilocksConfig>();
            let mut pw = PartialWitness::new();
            entry_t.set_targets(&mut pw, &DG1_DATA)?;
            let proof = data.prove(pw)?;
            let result = data.verify(proof);
        }
        Err(anyhow!(format!("Test passed with result : Passed ")))
    }

    /*#[test]
    fn test_date() -> anyhow::Result<()> {
        let data = parse_data(CBOR_DATA)?;
        println!("{:?}", data.data.keys());
        let birth_date_entry = data
            .data
            .get("birth_date")
            .ok_or_else(|| anyhow!("Could not find birth date"))?;
        let mut builder = CircuitBuilder::new(CircuitConfig::standard_recursion_config());
        let entry_t = EntryTarget::new(&mut builder, "birth_date", DataType::Date);
        let data = builder.build::<PoseidonGoldilocksConfig>();
        let mut pw = PartialWitness::new();
        entry_t.set_targets(&mut pw, &birth_date_entry.cbor)?;
        let proof = data.prove(pw)?;
        data.verify(proof)
    }*/

}
