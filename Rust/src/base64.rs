
use base64::alphabet::STANDARD as BASE64_ALPHABET;

pub trait Base64Convertible {
	fn to_base64(&self) -> String;
	fn of_base64(base64: &str) -> Self;
}
impl Base64Convertible for Vec<bool> {
	fn to_base64(&self) -> String {
		let mut result = String::new();
		for start_index in (0 .. self.len()).step_by(6) {
			let end_index = std::cmp::min(start_index + 6, self.len());
			let slice = &self[start_index .. end_index];
			let mut total = 0usize;
			let mut p = 1;
			for bit in slice {
				if *bit {
					total += p;
				}
				p *= 2;
			}
			result.push(BASE64_ALPHABET.as_str().chars().nth(total).unwrap());
		}
		result
	}
	fn of_base64(base64: &str) -> Self {
		let mut bools = vec![];
		for ch in base64.chars() {
			let mut index = BASE64_ALPHABET.as_str()
				.chars()
				.position(|x| x == ch)
				.unwrap();
			for _ in 0 .. 6 {
				bools.push(index % 2 == 1);
				index /= 2;
			}
		}
		bools
	}
}
