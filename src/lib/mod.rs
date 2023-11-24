pub fn run() {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn run_return_type() {
        assert_eq!(run(), ());
    }
}
