The `indexed::Pool`, a convenient allocator for index-linked data structures.

# Features

1. `Vec`-like operations.
  Supports `push()`, `reserve()` and random access by indexes which are similar with `std::Vec`'s methods.
  An unsafe `write()` method is provided, similar with `std::ptr::write()` except using index instead of pointer.

2. Using indexes to link elements to each other.
  Any element in the pool must implement `indexed::Indexed`, which stores its index in itself. A user-defined `null()` index indicates an empty linkage.

3. Obtaining reference of the pool from any one of its elements.
  This feature makes it possible to simply use reference of element instead of the style of using pool + index. It is convenient in some usecases because the library users do not need to store/pass the references of the pool everywhere.
  NOTICE: **this feature is unsafe** and it is the duty of the user not to violating memory safety.

4. No reallocation will happen.
Once an element is located in the pool, it will not move at all.

5. The pool can be managed or unmanaged.
  A managed pool owns its elements and drops them in destruction while an unmanaged pool does not.

# Performance

1. The underlying buffers are not continuous but segmented `Vec`s. Mapping conceptual index to underlying buffer address is as lightweight as doing one integer division.

2. The elements should provide space for storing its index. Index stored in usize occupies one extra pointer size. Index stored in u32 may occupy no extra space if some 32-bit hole exists in the struct in order to meet the alignment requirement. 

3. Obtaining the pool's reference from its element is as efficient as one pointer arithmetic and deference operation. Library users can pick the classic pool + index API style if not satisfied with this overhead.

4. Library users can pick up a different chunk size other than the default 256 for performance.

# License

Licensed under MIT.

# Example

See [API doc](https://docs.rs/indexed) for more.
