# `sharevec`

`sharevec` is a collection of reference counted, vector-like data structures. They are cheap to
clone, cloning in O(1) time, making sharing underlying memory very low cost. Variable (like `Vec`)
and fixed size, single and double-ended, and `Rc`/`Arc` versions are provided.

## Usage

Add `sharevec` to your dependencies with `cargo add sharevec`, or manually in your `Cargo.toml`:

```toml
[dependencies]
sharevec = "0.1.0"
```

```rust
fn main() {
    let mut vec: sharevec::RcVec<i32> = RcVec::new();
    // Can push to the vector as normal.
    vec.push(1);
    vec.push(2);
    vec.push(3);
    
    // Vector can be cloned without cloning the stored data.
    let shared: RcVec<_> = vec.clone();
    
    // Both the original and shared vectors have become immutable while shared.
    // Vectors must contain a "unique" reference to have elements added.
    assert!(vec.try_push(4).is_err());
    assert!(shared.try_push(4).is_err());
    
    // Shared vectors can have elements removed if copyable, without affecting the
    // other vector's memory.
    assert_eq!(vec.pop(), Some(3));
    assert_eq!(shared.len(), 3);
    
    // Dropping one of the vectors allows the other to be modified again.
    drop(vec);
    assert!(shared.try_push(4).is_ok());
}
```
