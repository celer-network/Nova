//! Benchmarks Nova's prover for proving SHA-256 with varying sized messages.
//! We run a single step with the step performing the entire computation.
//! This code invokes a hand-written SHA-256 gadget from bellman/bellperson.
//! It also uses code from bellman/bellperson to compare circuit-generated digest with sha2 crate's output
#![allow(non_snake_case)]
type G1 = pasta_curves::pallas::Point;
type G2 = pasta_curves::vesta::Point;
use ::bellperson::{
  gadgets::{
    boolean::{AllocatedBit, Boolean},
    num::{AllocatedNum, Num},
    //sha256::sha256,
    sha256::sha256iterated,
    Assignment,
  },
  ConstraintSystem, SynthesisError,
};
use ff::{PrimeField, PrimeFieldBits};
use hex_literal::hex;
use flate2::{write::ZlibEncoder, Compression};
use nova_snark::{
  traits::{
    circuit::{StepCircuit, TrivialTestCircuit},
    Group,
  },
  CompressedSNARK, PublicParams, RecursiveSNARK,
};
use sha2::{Digest, Sha256};
use criterion::*;
use core::time::Duration;
use std::time::Instant;

// Imports related to Poseidon hash function (unused for now)
/*
use nova_snark::traits::{ROCircuitTrait, ROConstantsTrait, ROTrait};
use generic_array::typenum::U24;
use neptune::{
  circuit2::Elt,
  poseidon::PoseidonConstants,
  sponge::{
    api::{IOPattern, SpongeAPI, SpongeOp},
    circuit::SpongeCircuit,
    vanilla::{Mode::Simplex, Sponge, SpongeTrait},
  },
  Strength,
};
use nova_snark::provider::poseidon::PoseidonRO;
use nova_snark::provider::poseidon::PoseidonConstantsCircuit;
 */

// Number if iterations of the sha256 function implemented by the
// gadget
const NITERATIONS: usize = 100;
// Number of Nova steps (resp. foldings) over which we are producing
// the final Nova proof
const NSTEPS: usize = 10;

/*
#[derive(Clone, Debug)]
struct Sha256CircuitOrig<Scalar: PrimeField> {
  preimage: Vec<u8>,
  digest: Scalar,
}
*/

#[derive(Clone, Debug)]
struct Sha256Circuit<Scalar: PrimeField> {
  preimage: Vec<u8>,
  // digest: Vec<Scalar>,
  digest: Scalar,
}

impl<Scalar: PrimeField + PrimeFieldBits> StepCircuit<Scalar> for Sha256Circuit<Scalar> {
    fn arity(&self) -> usize {
	1
    }

    fn synthesize<CS: ConstraintSystem<Scalar>>(
	&self,
	cs: &mut CS,
	_z: &[AllocatedNum<Scalar>],
    ) -> Result<Vec<AllocatedNum<Scalar>>, SynthesisError> {

	assert_eq!(self.preimage.len(), 64 * (NITERATIONS as usize));
	
	let mut z_out: Vec<AllocatedNum<Scalar>> = Vec::new();

	let bit_values: Vec<_> =	  
	    self.preimage.clone().into_iter().flat_map(|byte| (0..8).map(move |i| (byte >> i) & 1u8 == 1u8)).map(Some).collect();
	assert_eq!(bit_values.len(), self.preimage.len() * 8);

	let preimage_bits = bit_values
	    .into_iter()
	    .enumerate()
	    .map(|(i, b)| AllocatedBit::alloc(cs.namespace(|| format!("preimage bit {i}")), b))
	    .map(|b| b.map(Boolean::from))
	    .collect::<Result<Vec<_>, _>>()?;

	let niterations: usize = NITERATIONS;
	let hash_bits = sha256iterated(cs.namespace(|| "sha256"), &preimage_bits, niterations)?;

	for (i, hash_bits) in hash_bits.chunks(256_usize).enumerate() {
	    let mut num = Num::<Scalar>::zero();
	    let mut coeff = Scalar::one();
	    for bit in hash_bits {
		num = num.add_bool_with_coeff(CS::one(), bit, coeff);

		coeff = coeff.double();
	    }

	    let hash = AllocatedNum::alloc(cs.namespace(|| format!("input {i}")), || {
		Ok(*num.get_value().get()?)
	    })?;

	    // num * 1 = hash
	    cs.enforce(
		|| format!("packing constraint {i}"),
		|_| num.lc(Scalar::one()),
		|lc| lc + CS::one(),
		|lc| lc + hash.get_variable(),
	    );
	    z_out.push(hash);
	}	

	// sanity check with the hasher Prepare a zero vector of 64
	// bytes. Note: we are not using &self.preimage member of the
	// gadget as it represents a vector of zero 64-byte vectors
	let preimage = vec![0u8; 64];
		
	let mut hasher = Sha256::new();
	// hasher.update(&self.preimage);
	hasher.update(preimage);
	let hash_result = hasher.finalize();

	let mut s = hash_result
	    .iter()
	    .flat_map(|&byte| (0..8).rev().map(move |i| (byte >> i) & 1u8 == 1u8));

	for b in &hash_bits {
	    match b {
		Boolean::Is(b) => {
		    assert!(s.next().unwrap() == b.get_value().unwrap());
		}
		Boolean::Not(b) => {
		    assert!(s.next().unwrap() != b.get_value().unwrap());
		}
		Boolean::Constant(_b) => {
		    panic!("Can't reach here")
		}
	    }
	}
	
	// println!("z_out length {:?}", z_out.len());
	Ok(z_out)
    }

    fn output(&self, _z: &[Scalar]) -> Vec<Scalar> {
	vec![self.digest]
	//self.digest.clone()
    }
}

type C1 = Sha256Circuit<<G1 as Group>::Scalar>;
type C2 = TrivialTestCircuit<<G2 as Group>::Scalar>;

criterion_group! {
name = recursive_snark;
config = Criterion::default().warm_up_time(Duration::from_millis(3000));
targets = bench_recursive_snark
}

criterion_main!(recursive_snark);

fn bench_recursive_snark(_c: &mut Criterion) {
    println!("=========================================================");
    println!("{NITERATIONS} non-recursive SHA256 iterations");
    println!("{NSTEPS} Nova steps");
    
    let bytes_to_scalar = |bytes: [u8; 32]| -> <G1 as Group>::Scalar {
	let mut bytes_le = bytes;
	bytes_le.reverse();
	<G1 as Group>::Scalar::from_repr(bytes_le).unwrap()
    };

    // return single hash
    let circuit_primary =
	Sha256Circuit {
	    preimage: vec![0u8; 64 * (NITERATIONS as usize)],
	    digest: bytes_to_scalar(hex!(
		"12df9ae4958c1957170f9b04c4bc00c27315c5d75a391f4b672f952842bfa5ac"
	    )),
	};

    // Produce public parameters
    let pp = PublicParams::<G1, G2, C1, C2>::setup(
	circuit_primary.clone(),
	TrivialTestCircuit::default(),
    );
    println!(
      "Number of constraints per step (primary circuit): {}",
      pp.num_constraints().0
    );
    println!(
      "Number of constraints per step (secondary circuit): {}",
      pp.num_constraints().1
    );

    println!(
      "Number of variables per step (primary circuit): {}",
      pp.num_variables().0
    );
    println!(
      "Number of variables per step (secondary circuit): {}",
      pp.num_variables().1
    );
    
    // Produce SNARK for multiple steps
    let num_steps = NSTEPS;
    let sha256_circuits = (0..num_steps)
	.map(|_| Sha256Circuit{
	    preimage: vec![0u8; 64 * (NITERATIONS as usize)],
	    digest: bytes_to_scalar(hex!(
		"12df9ae4958c1957170f9b04c4bc00c27315c5d75a391f4b672f952842bfa5ac"
	    )),
	}).collect::<Vec<_>>(); 

    // Produce a recursive SNARK
    println!("Generating a RecursiveSNARK...");
    let mut recursive_snark: Option<RecursiveSNARK<G1, G2, C1, C2>> = None;
    
    for (i, circuit_primary) in sha256_circuits.iter().take(num_steps).enumerate() {
	let start = Instant::now();
	let res = RecursiveSNARK::prove_step
	    (
		black_box(&pp),
		//black_box(None),
                recursive_snark,
		black_box(circuit_primary.clone()),
		black_box(TrivialTestCircuit::default()),
		black_box(vec![<G1 as Group>::Scalar::from(2u64)]),
		black_box(vec![<G2 as Group>::Scalar::from(2u64)]),
	    );
      assert!(res.is_ok());
      println!(
        "RecursiveSNARK::prove_step {}: {:?}, took {:?} ",
        i,
        res.is_ok(),
        start.elapsed()
      );
      recursive_snark = Some(res.unwrap());
    }

    assert!(recursive_snark.is_some());
    let recursive_snark = recursive_snark.unwrap();
    
    // verify the recursive SNARK
    println!("Verifying a RecursiveSNARK...");
    let start = Instant::now();
    let res = recursive_snark.verify(&pp, num_steps, black_box(vec![<G1 as Group>::Scalar::from(2u64)]), black_box(vec![<G2 as Group>::Scalar::from(2u64)]));
    println!(
      "RecursiveSNARK::verify: {:?}, took {:?}",
      res.is_ok(),
      start.elapsed()
    );
    assert!(res.is_ok());
    
    // produce a compressed SNARK
    println!("Generating a CompressedSNARK using Spartan with IPA-PC...");
    let (pk, vk) = CompressedSNARK::<_, _, _, _, S1, S2>::setup(&pp).unwrap();
    
    let start = Instant::now();
    type EE1 = nova_snark::provider::ipa_pc::EvaluationEngine<G1>;
    type EE2 = nova_snark::provider::ipa_pc::EvaluationEngine<G2>;
    type S1 = nova_snark::spartan::RelaxedR1CSSNARK<G1, EE1>;
    type S2 = nova_snark::spartan::RelaxedR1CSSNARK<G2, EE2>;

    let res = CompressedSNARK::<_, _, _, _, S1, S2>::prove(&pp, &pk, &recursive_snark);
    println!(
      "CompressedSNARK::prove: {:?}, took {:?}",
      res.is_ok(),
      start.elapsed()
    );
    assert!(res.is_ok());
    let compressed_snark = res.unwrap();
    
    let mut encoder = ZlibEncoder::new(Vec::new(), Compression::default());
    bincode::serialize_into(&mut encoder, &compressed_snark).unwrap();
    let compressed_snark_encoded = encoder.finish().unwrap();
    println!(
      "CompressedSNARK::len {:?} bytes",
      compressed_snark_encoded.len()
    );
    
    // verify the compressed SNARK
    println!("Verifying a CompressedSNARK...");
    let start = Instant::now();
    let res = compressed_snark.verify(&vk, num_steps, black_box(vec![<G1 as Group>::Scalar::from(2u64)]), black_box(vec![<G2 as Group>::Scalar::from(2u64)]));
    println!(
      "CompressedSNARK::verify: {:?}, took {:?}",
      res.is_ok(),
      start.elapsed()
    );
    assert!(res.is_ok());
    println!("=========================================================");
}
