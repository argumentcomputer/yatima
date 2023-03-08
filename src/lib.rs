use blake3::hash;

#[no_mangle]
extern "C" fn blake3(mem: &mut [u8; 32], len: usize, input: *const u8) {
  unsafe {
    *mem = *hash(std::slice::from_raw_parts(input, len)).as_bytes();
  }
} 
