//! **Machine-checked proofs (Kani) of the inert-configuration page**: the reader never panics,
//! whatever the page holds; it answers only a member of a key's list, and only the member the field
//! holds; and every page the builder writes reads back as the members it was given. Behind
//! `#[cfg(kani)]`, so only `cargo kani` compiles them.

use super::*;

/// Any one member of `list`, chosen by the model checker.
fn any_member(list: &'static [&'static str]) -> &'static str {
    let index: usize = kani::any();
    kani::assume(index < list.len());
    list[index]
}

/// Falsification: replayable `falsifications/verification.field_bytes_never_panics_for_any_length_byte.patch`
/// **`field_bytes`, which every accessor reads through, never panics for any length byte, and a
/// length past the field reads as absent.**
/// The page is the real size, `TERM`'s field is the last on it, and the length byte is free, so the
/// case that once sliced past the end of the page (a length of 255) is among the inputs.
#[kani::proof]
#[kani::unwind(2)]
fn field_bytes_never_panics_for_any_length_byte() {
    let mut page = [0u8; PAGE_CONTENT_BYTES];
    let length: u8 = kani::any();
    page[TERMINAL_TYPE_LENGTH_OFFSET_BYTES] = length;
    let read = field_bytes(
        &page,
        TERMINAL_TYPE_LENGTH_OFFSET_BYTES,
        TERMINAL_TYPE_OFFSET_BYTES,
        MAXIMUM_TERMINAL_TYPE_BYTES,
    );
    if usize::from(length) > MAXIMUM_TERMINAL_TYPE_BYTES {
        assert!(read.is_none());
    }
}

/// Falsification: replayable `falsifications/verification.any_members_round_trip.patch`
/// **For any one member of each list, the page `PageBuilder` builds reads back as those three
/// members.**
#[kani::proof]
#[kani::unwind(42)]
fn any_members_round_trip() {
    let time_zone = any_member(domain::KNOWN_TIME_ZONES);
    let locale = any_member(domain::KNOWN_LOCALES);
    let terminal_type = any_member(domain::KNOWN_TERMINAL_TYPES);
    let page = PageBuilder::new()
        .time_zone(time_zone)
        .unwrap()
        .locale(locale)
        .unwrap()
        .terminal_type(terminal_type)
        .unwrap()
        .build();
    let read = ConfigurationView::new(&page);
    assert_eq!(read.time_zone(), Some(time_zone));
    assert_eq!(read.locale(), Some(locale));
    assert_eq!(read.terminal_type(), Some(terminal_type));
}

/// Whether the page's field holds exactly `value`'s bytes: its length byte is the value's length,
/// and the bytes after it are the value's.
fn field_holds(
    page: &[u8; PAGE_CONTENT_BYTES],
    length_offset: usize,
    value_offset: usize,
    value: &str,
) -> bool {
    usize::from(page[length_offset]) == value.len()
        && page[value_offset..value_offset + value.len()] == *value.as_bytes()
}

/// Falsification: replayable `falsifications/verification.an_accessor_answers_only_the_member_its_field_holds.patch`
/// **For any page at all, each accessor answers either `None` or a member of its key's list, and
/// then only on a page that carries the magic and whose field holds exactly that member.** No
/// input makes a reader panic, and no input makes it answer a value the page does not carry.
#[kani::proof]
#[kani::unwind(42)]
fn an_accessor_answers_only_the_member_its_field_holds() {
    let page: [u8; PAGE_CONTENT_BYTES] = kani::any();
    let read = ConfigurationView::new(&page);
    let recognized = page[MAGIC_OFFSET_BYTES..MAGIC_OFFSET_BYTES + 8] == MAGIC;
    if let Some(value) = read.time_zone() {
        assert!(recognized);
        assert!(domain::KNOWN_TIME_ZONES.contains(&value));
        assert!(field_holds(
            &page,
            TIME_ZONE_LENGTH_OFFSET_BYTES,
            TIME_ZONE_OFFSET_BYTES,
            value
        ));
    }
    if let Some(value) = read.locale() {
        assert!(recognized);
        assert!(domain::KNOWN_LOCALES.contains(&value));
        assert!(field_holds(
            &page,
            LOCALE_LENGTH_OFFSET_BYTES,
            LOCALE_OFFSET_BYTES,
            value
        ));
    }
    if let Some(value) = read.terminal_type() {
        assert!(recognized);
        assert!(domain::KNOWN_TERMINAL_TYPES.contains(&value));
        assert!(field_holds(
            &page,
            TERMINAL_TYPE_LENGTH_OFFSET_BYTES,
            TERMINAL_TYPE_OFFSET_BYTES,
            value
        ));
    }
}
