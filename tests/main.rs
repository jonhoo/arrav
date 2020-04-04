use arrav::Arrav;

#[test]
fn basics() {
    let mut v: Arrav<u8, 4> = Default::default();
    assert_eq!(v.len(), 0);
    assert_eq!(v.capacity(), 4);
    assert!(v.is_empty());

    v.try_push(0).unwrap();
}
