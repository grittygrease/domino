use super::parse_model;
use crate::assert_matches;

#[test]
fn parse_model_files() {
    let file = std::fs::File::open("src/util/smtparser/testdata/model.smt2").unwrap();
    let content = std::io::read_to_string(file).unwrap();

    let (model, length) = parse_model(&content).unwrap();
    dbg!(&model);

    assert_eq!(length, 3209);
    assert_eq!(
        model.get_value_as_int("randctr-small_composition-0"),
        Some(0)
    );
    assert_eq!(model.get_value_as_bool("<equal-aborts>"), Some(true));
}

#[test]
fn only_parses_one_model() {
    let file = std::fs::File::open("src/util/smtparser/testdata/model_double.smt2").unwrap();
    let content = std::io::read_to_string(file).unwrap();

    let (_model, length) = parse_model(&content).unwrap();

    assert_eq!(length, 3209);
}

#[test]
fn parsing_half_model_fails() {
    let file = std::fs::File::open("src/util/smtparser/testdata/model_half.smt2").unwrap();
    let content = std::io::read_to_string(file).unwrap();

    assert_matches!(parse_model(&content), Err(_));
}

#[test]
fn parses_bitvector_and_sequence_values() {
    let content = "(\n(define-fun b () (_ BitVec 8) #b00000001)\n(define-fun h () (_ BitVec 8) #xff)\n(define-fun s () (Seq (_ BitVec 8)) (seq.++ (seq.unit #b00000000) (as seq.empty (Seq (_ BitVec 8)))))\n)\n";
    let (_model, length) = parse_model(content).unwrap();
    assert_eq!(length, content.trim_end().len());
}

#[test]
fn keeps_integers_wider_than_i32() {
    let content = "(\n(define-fun wide () Int 123456789012345678901234567890)\n(define-fun small () Int 7)\n)\n";
    let (model, _length) = parse_model(content).unwrap();
    assert_eq!(model.get_value_as_int("small"), Some(7));
    assert_eq!(model.get_value_as_int("wide"), None);
}
