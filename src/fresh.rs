use crate::types::Symbol;

pub fn freshen(used: &[Symbol], x: Symbol) -> Symbol {
    if used.contains(&x) {
        let split = split_name(&x.name);
        freshen_split(used, split)
    } else {
        x
    }
}

fn freshen_split(used: &[Symbol], split: (&str, u64)) -> Symbol {
    let joined = unsplit_name(split);
    if used.contains(&joined) {
        freshen_split(used, next_split_name(split))
    } else {
        joined
    }
}

fn is_name_digit(c: &char) -> bool {
    "0123456789₀₁₂₃₄₅₆₇₈₉".contains(*c)
}

fn split_name(t: &str) -> (&str, u64) {
    match t.chars().rev().take_while(is_name_digit).count() {
        0 => (t, 1),
        n if n == t.chars().count() => {
            let others = "x";
            let digits = as_non_subscript(t);
            (others, digits.parse().unwrap())
        }
        mid => {
            let len = t.len();
            let (others, digits) = t.split_at(mid);
            let others = if others.is_empty() { "x" } else { others };
            let digits = if digits.is_empty() {
                "1".to_owned()
            } else {
                as_non_subscript(digits)
            };
            (others, digits.parse().unwrap())
        }
    }
}

fn next_split_name(arg: (&str, u64)) -> (&str, u64) {
    let (base, i) = arg;
    (base, i + 1)
}

fn unsplit_name(arg: (&str, u64)) -> Symbol {
    let (base, i) = arg;
    let name = format!("{}{}", base, as_subscript(&i.to_string()));
    Symbol { name }
}

fn as_non_subscript(digits: &str) -> String {
    digits.chars().map(|c| swap_if(c, true)).collect()
}

fn as_subscript(digits: &str) -> String {
    digits.chars().map(|c| swap_if(c, false)).collect()
}

fn swap_if(c: char, as_non_subscript: bool) -> char {
    let f = SUBSCRIPT_DIGITS
        .iter()
        .find(|(d, s)| if as_non_subscript { s == &c } else { d == &c });
    match f {
        Some((d, s)) => {
            if as_non_subscript {
                *d
            } else {
                *s
            }
        }
        None => c,
    }
}

const SUBSCRIPT_DIGITS: &[(char, char)] = &[
    ('0', '₀'),
    ('1', '₁'),
    ('2', '₂'),
    ('3', '₃'),
    ('4', '₄'),
    ('5', '₅'),
    ('6', '₆'),
    ('7', '₇'),
    ('8', '₈'),
    ('9', '₉'),
];

#[cfg(test)]
mod tests {
    use crate::{fresh::freshen, types::Symbol};

    #[test]
    fn test_fresh_names() {
        fn sym(name: &str) -> Symbol {
            let name = name.to_owned();
            Symbol { name }
        }
        let cases: &[(&[Symbol], _, _)] = &[
            (&[sym("x")], sym("x"), sym("x₁")),
            (&[sym("x"), sym("x₁"), sym("x₂")], sym("x"), sym("x₃")),
            (&[sym("x"), sym("x1"), sym("x2")], sym("y"), sym("y")),
            (
                &[sym("r2d"), sym("r2d₀"), sym("r2d₁")],
                sym("r2d"),
                sym("r2d₂"),
            ),
            (&[], sym("A"), sym("A")),
            (&[sym("x₁")], sym("x₁"), sym("x₂")),
            (&[], sym("x₁"), sym("x₁")),
            (&[], sym("₉₉"), sym("₉₉")),
            (&[sym("₉₉")], sym("₉₉"), sym("x₉₉")),
            (&[sym("₉₉"), sym("x₉₉")], sym("₉₉"), sym("x₁₀₀")),
        ];
        for (used, x, expected) in cases {
            let actual = freshen(used, x.clone());
            assert_eq!(expected, &actual);
        }
    }
}
