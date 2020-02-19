// See the COPYRIGHT file at the top-level directory of this distribution.
// Licensed under MIT license <LICENSE-MIT or http://opensource.org/licenses/MIT>

//! This library provides a `Vec`-like, no reallocation collection named `indexed::Pool`.
//! The pool's reference can be obtained from one of its elements.
//! It can be used as a memory pool, and library users do not need to store/pass the pool's reference everywhere.
//! The elements can be linked to each other using indexes rather than pointers.
//!
//! # Examples
//!
//! ```
//! use indexed::{Indexed,Pool};
//! use std::fmt::{self,Display,Formatter};
//!
//! // A singly linked list of string.
//! struct List( Box<Pool<Node>> );
//!
//! struct Node {
//!     next  : u32,
//!     index : u32,
//!     text  : &'static str,
//! }
//!
//! unsafe impl Indexed for Node {
//!     fn null() -> usize { !0_u32 as usize }
//!     unsafe fn get_index( &self ) -> usize { self.index as usize }
//!     unsafe fn set_index( &mut self, index: usize ) { self.index = index as u32; }
//! }
//!
//! impl List {
//!     fn new() -> Self { List( Pool::<Node>::new() )}
//!
//!     fn head<'a>( &'a mut self, text: &'static str ) -> &'a mut Node {
//!         assert_eq!( self.0.new_index(), 0 );
//!         self.0.push( Node{
//!             next  : Node::null() as u32,
//!             index : 0, // the pool will set the actual index inside its `push()` method.
//!             text  ,
//!         });
//!         &mut self.0[0]
//!     }
//! }
//!
//! impl Node {
//!     // The method does not need a parameter of `Pool`.
//!     fn add<'a>( &'a mut self, sib: &'static str ) -> &'a mut Self {
//!         let pool = unsafe { self.pool_mut() as *mut Pool<Node> };
//!         let index = unsafe{ (*pool).new_index() };
//!         self.next = index as u32;
//!         let pool = unsafe{ &mut *pool };
//!         pool.push( Node{
//!             next  : Node::null() as u32,
//!             index : Node::null() as u32, // the pool will set the actual index inside its `push()` method.
//!             text  : sib,
//!         });
//!         &mut pool[index]
//!     }
//! }
//!
//! impl Display for List {
//!     fn fmt( &self, fmt: &mut Formatter ) -> fmt::Result {
//!         if self.0.new_index() != 0 {
//!             let mut curr = 0_usize;
//!             while curr != Node::null() {
//!                 write!( fmt, "{} ", self.0[curr].text )?;
//!                 curr = self.0[curr].next as usize;
//!             }
//!         }
//!         Ok(())
//!     }
//! }
//!
//! let mut list = List::new();
//! list.head( "no" ).add( "need" ).add( "for" ).add( "pool" ).add( "parameter" );
//! assert_eq!( list.to_string(), "no need for pool parameter " );
//! ```

#![cfg_attr( feature = "no_std", no_std )]
#![cfg_attr( feature = "no_std", feature( alloc ))]

#[cfg(not(feature="no_std"))] pub(crate) use std::boxed::Box;
#[cfg(not(feature="no_std"))] pub(crate) use std::fmt::{self,Debug};
#[cfg(not(feature="no_std"))] pub(crate) use std::marker::PhantomData;
#[cfg(not(feature="no_std"))] pub(crate) use std::mem::{self,transmute};
#[cfg(not(feature="no_std"))] pub(crate) use std::ops;
#[cfg(not(feature="no_std"))] pub(crate) use std::pin::Pin;
#[cfg(not(feature="no_std"))] pub(crate) use std::ptr::{self,NonNull,drop_in_place};

#[cfg(feature="no_std")] extern crate alloc;
#[cfg(feature="no_std")] pub(crate) use self::alloc::boxed::Box;
#[cfg(feature="no_std")] pub(crate) use self::alloc::vec::Vec;
#[cfg(feature="no_std")] pub(crate) use core::fmt::{self,Debug};
#[cfg(feature="no_std")] pub(crate) use core::marker::PhantomData;
#[cfg(feature="no_std")] pub(crate) use core::mem::{self,transmute};
#[cfg(feature="no_std")] pub(crate) use core::ops;
#[cfg(feature="no_std")] pub(crate) use core::pin::Pin;
#[cfg(feature="no_std")] pub(crate) use core::ptr::{self,NonNull,drop_in_place};

/// Possible chunk sizes.
pub enum ChunkLen {
    B5 = 32, B6 = 64, B7 = 128, B8 = 256, B9 = 512, B10 = 1024, B11 = 2048, B12 = 4096, B13 = 8192, B14 = 16384, B15 = 32768, B16 = 65536,
}

/// Reflects the count of elements a chunk can hold.
pub fn chunk_len<T:Indexed>() -> usize { <T as Indexed>::chunk_len() as isize as usize }

/// Type of elements in the `Pool` must implement this trait.
/// Typically some integer field in the type must devote to storing the index in the pool, and it is not necessarily usize.
/// For example, an index can be stored in u32 if 4194304K is enough for anybody.
pub unsafe trait Indexed: Sized {
    /// Sets the underlying chunk size. The default is 256, and can be overrided by those values defined in `ChunkLen`.
    fn chunk_len() -> ChunkLen { ChunkLen::B8 }

    /// Defines which index value is for null. If the underlying storage for index is smaller than `usize`'s size, the library user should override this method and pick a smaller value, e.g `!0_u32` for index stored in `u32`.
    /// Note that it is for convenience only, and the library will not do any index check against `null()`.
    fn null() -> usize { !0_usize }

    /// Gets the element's index in the pool.
    unsafe fn get_index( &self ) -> usize;

    /// Sets the element's index in the pool. The library user is not expected to call it directly.
    unsafe fn set_index( &mut self, index: usize );

    /// Obtains reference of its pool.
    fn pool( &self ) -> &Pool<Self> { Pool::pool( self )}

    /// Obtains mutable reference of its pool.
    unsafe fn pool_mut( &self ) -> &mut Pool<Self> { Pool::pool_mut( self )}

    /// Obtains non null pointer of its pool.
    fn pool_non_null( &self ) -> NonNull<Pool<Self>> { unsafe{ NonNull::new_unchecked( Pool::pool_mut( self ))}}

    /// Appends an element to the back of its pool.
    fn pool_push( &self, value: Self ) { unsafe{ self.pool_mut().push( value )}}

    /// Overwrites a new value into its pool at given index without reading or dropping the old value.
    unsafe fn pool_write( &self, index: usize, value: Self ) { self.pool_mut().write( index, value ); }

    /// Reserves capacity for at least additional more elements to be inserted in the given Pool<T>.
    /// The collection may reserve more space because the increasing size must be multiple of underlying `chunk_len()`.
    /// After calling reserve, capacity will be greater than or equal to self.pool().new_index() + additional.
    /// Does nothing if capacity is already sufficient.
    fn pool_reserve( &self, additional: usize ) { unsafe{ self.pool_mut().reserve( additional ); }}
}

#[derive(PartialEq,Eq)]
struct Chunk<T>( Vec<u8>, PhantomData<T> );

type PPool<T> = NonNull<Pool<T>>;

impl<T:Indexed> Chunk<T> {
    #[inline] fn data_size() -> usize { mem::size_of::<[T;1]>() * chunk_len::<T>() }

    #[inline] fn buffer_size() -> usize { Self::data_size() + mem::size_of::<PPool<T>>() }

    #[inline] fn as_ptr( &self ) -> *const T { self.0.as_ptr() as *const T }
    #[inline] fn as_mut_ptr( &mut self ) -> *mut T { self.0.as_mut_ptr() as *mut T }

    #[inline] fn data_ptr( &self, index: usize ) -> *const T { unsafe{( self.as_ptr() ).add( index )}}
    #[inline] fn data_mut_ptr( &mut self, index: usize ) -> *mut T { unsafe{( self.as_mut_ptr() ).add( index )}}

    #[inline] fn ppool( &self ) -> *const PPool<T> { self.data_ptr( chunk_len::<T>() ) as *const PPool<T> }

    #[inline] fn new( ppool: PPool<T> ) -> Self {
        let mut buffer = Vec::<u8>::with_capacity( Self::buffer_size() );
        unsafe {
            ptr::write( buffer.as_mut_ptr().add( Self::data_size() ) as *mut NonNull<_>, ppool );
        }
        Chunk( buffer, PhantomData )
    }

    #[inline] fn write( &mut self, index: usize, value: T ) {
        assert!( index <= chunk_len::<T>() );
        unsafe{ ptr::write( self.data_mut_ptr( index ), value )};
    }
}

impl<T:Indexed+Debug> Debug for Chunk<T> {
    fn fmt( &self, fmt: &mut fmt::Formatter ) -> fmt::Result {
        let mut p = self.as_ptr();
        let mut count = chunk_len::<T>();
        let mut buffer = Vec::with_capacity( count );
        while count > 0 {
            buffer.push( unsafe{ ptr::read( p )});
            unsafe{ p = p.offset(1) };
            count -= 1;
        }
        fmt.write_str( "\n" )?;
        fmt.debug_struct( "Chunk" )
            .field( "ppool", unsafe{ &ptr::read( self.ppool() )})
            .field( "buffer", &buffer )
            .finish()?; 
        unsafe{ buffer.set_len(0); }
        Ok(())
    }
}

impl<T:Indexed> ops::Index<usize> for Chunk<T> {
    type Output = T;
    fn index( &self, index: usize ) -> &T { unsafe{ &*self.data_ptr( index )}}
}

impl<T:Indexed> ops::IndexMut<usize> for Chunk<T> {
    fn index_mut( &mut self, index: usize ) -> &mut T { unsafe{ &mut *self.data_mut_ptr( index )}}
}

/// A `Vec`-like, no reallocation collection.
/// Elements in a `Pool` should not be zero sized type, or the construction will panic.
#[derive(Debug,PartialEq,Eq)]
pub struct Pool<T:Indexed> {
    chunks  : Vec<Chunk<T>>, // underlying storage.
    managed : bool,          // whether drops elements on destruction or not.
    ppool   : PPool<T>,      // NonNull pointer to self.
    subidx  : usize,         // index of last element in its chunk, or `chunk_len::<T>()-1` if no element in the pool at all.
    len     : usize,         // element count of the pool.
    cap     : usize,         // capacity of the pool, always multiple of `chunk_len::<T>()`.
}

impl<T:Indexed> Pool<T> {
    /// Creates a new pool that drops its elements on destruction.
    ///
    /// # Panics
    ///
    /// Panics if the type of element is ZST.
    ///
    /// # Examples
    ///
    /// ```
    /// #[macro_use] extern crate indexed;
    /// use indexed::{Indexed,Pool};
    ///
    /// static mut COUNT: usize = 0;
    ///
    /// struct Name { index: usize, text: String }
    ///
    /// impl_indexed!{ Name{ index: usize }}
    ///
    /// impl Drop for Name { fn drop( &mut self ) { unsafe{ COUNT += 1; }}}
    ///
    /// impl From<&'static str> for Name {
    ///     fn from( s: &'static str ) -> Self {
    ///         Name{ index: <Self as Indexed>::null(), text: s.to_string() }
    ///     }
    /// }
    ///
    /// { let pool = pool!( Name[ "foo", "bar", "baz" ]); }
    ///
    /// assert_eq!( unsafe{ COUNT }, 3 );
    /// ```
    pub fn new() -> Box<Self> { Self::new_pool( true )}

    /// Creates a new pool that does not drop its elements on destruction.
    /// It is up to the user to drop the elements manually to avoid memory leaks.
    ///
    /// # Panics
    ///
    /// Panics if the type of element is ZST.
    ///
    /// # Examples
    ///
    /// ```
    /// #[macro_use] extern crate indexed;
    /// use indexed::{Indexed,Pool};
    ///
    /// static mut COUNT: usize = 0;
    ///
    /// struct Name { index: usize, text: String }
    ///
    /// impl_indexed!{ Name{ index: usize }}
    ///
    /// impl Drop for Name { fn drop( &mut self ) { unsafe{ COUNT += 1; }}}
    ///
    /// impl From<&'static str> for Name {
    ///     fn from( s: &'static str ) -> Self {
    ///         Name{ index: <Self as Indexed>::null(), text: s.to_string() }
    ///     }
    /// }
    ///
    /// {
    ///     let mut pool = Pool::<Name>::new_unmanaged();
    ///     pool.push( "foo".into() );
    ///     pool.push( "bar".into() );
    ///     pool.push( "baz".into() );
    /// }
    /// assert_eq!( unsafe{ COUNT }, 0 );
    /// ```
    pub fn new_unmanaged() -> Box<Self> { Self::new_pool( false )}

    fn new_pool( managed: bool ) -> Box<Self> {
        if mem::size_of::<T>() == 0 {
            panic!( "ZSTs are not allowed to be the `Pool`'s element type." );
        } else {
            let pool = Box::new( Self {
                chunks  : Vec::new(),
                managed , 
                ppool   : NonNull::dangling(),
                subidx  : chunk_len::<T>()-1,
                len     : 0,
                cap     : 0,
            });
            unsafe {
                let pool = Box::into_raw( pool );
                let ppool = NonNull::new_unchecked( pool );
                let mut pool = Box::from_raw( pool );
                pool.ppool = ppool;
                pool
            }
        }
    }

    /// Appends an element to the back of a pool.
    ///
    /// # Panics
    ///
    /// Panics if the number of elements in the vector overflows a `usize`.
    ///
    /// # Examples
    ///
    /// ```
    /// #[macro_use] extern crate indexed;
    /// use indexed::{Indexed,Pool};
    ///
    /// extrusive_indexed!{ Foo{ inner: i32 }}
    ///
    /// let mut pool = Pool::new();
    ///
    /// pool.push( Foo::from( 0 ));
    /// pool.push( Foo::from( 1 ));
    /// pool.push( Foo::from( 2 ));
    ///
    /// assert_eq!( pool.iter().map( |e| e.inner ).collect::<Vec<_>>(), vec![ 0, 1, 2 ]);
    /// ```
    pub fn push( &mut self, mut value: T ) {
        self.subidx += 1;
        let chunk_len = chunk_len::<T>();
        if self.subidx == chunk_len {
            if self.len == Self::check( self.chunks.len(), usize::checked_mul, chunk_len ) {
                self.chunks.push( Chunk::new( self.ppool ));
                self.cap += chunk_len;
            }
            self.subidx = 0;
        }
        let len = self.len;
        unsafe{ value.set_index( len )};
        self.chunks.last_mut().unwrap().write( self.subidx, value );
        self.len += 1;
    }

    /// Overwrites a new value into a pool at given index without reading or dropping the old value.
    ///
    /// # Safety
    ///
    /// This operation is marked unsafe because it accepts an index as an offset which acts like a raw pointer.
    ///
    /// It does not drop the contents of the existing `self[index]` element. This is safe, but it could leak allocations or resources,
    /// so care must be taken not to overwrite an object that should be dropped.
    ///
    /// Additionally, it does not drop `value`. Semantically, `value` is moved into `self[index]`.
    ///
    /// This is appropriate for initializing uninitialized memory.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// #[macro_use] extern crate indexed;
    /// use indexed::{Indexed,Pool};
    ///
    /// extrusive_indexed!{ Foo{ inner: &'static str }}
    ///
    /// let mut pool = Pool::<Foo>::new();
    ///
    /// pool.reserve( 3 );
    ///
    /// unsafe {
    ///     pool.write( 0, "a".into() );
    ///     pool.write( 2, "c".into() );
    ///     pool.write( 1, "b".into() );
    ///     pool.set_len( 3 );
    /// }
    ///
    /// assert_eq!( pool.iter().map( |e| e.inner ).collect::<Vec<_>>(), vec![ "a", "b", "c" ]);
    /// ```
    #[inline]
    pub unsafe fn write( &mut self, index: usize, mut value: T ) {
        value.set_index( index );
        self.chunks[ index / chunk_len::<T>() ].write( index % chunk_len::<T>(), value );
    }

    /// Reserves capacity for at least additional more elements to be inserted in the given Pool<T>.
    /// The collection may reserve more space because the increasing size must be multiple of underlying `chunk_len()`.
    /// After calling reserve, capacity will be greater than or equal to self.new_index() + additional.
    /// Does nothing if capacity is already sufficient.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows `usize`.
    ///
    /// # Examples
    ///
    /// ```
    /// #[macro_use] extern crate indexed;
    /// use indexed::{Indexed,Pool};
    ///
    /// extrusive_indexed!{ Foo{ inner: &'static str }}
    ///
    /// let mut pool = Pool::<Foo>::new();
    ///
    /// pool.reserve( 0 );
    /// assert_eq!( pool.capacity(), 0 );
    ///
    /// pool.reserve( 1 );
    /// let cap = pool.capacity();
    /// assert!( cap >= 1 );
    ///
    /// pool.reserve( 1 );
    /// assert_eq!( pool.capacity(), cap );
    ///
    /// pool.reserve( 1024 );
    /// assert!( pool.capacity() >= 1024 );
    /// ```
    pub fn reserve( &mut self, additional: usize ) {
        if let Some( inc_cap ) = self.check_len( usize::checked_add, additional ) // self.len + additional
                                     .checked_sub( self.cap )                     // - self.cap
        {
            let mut chunk_count = inc_cap / chunk_len::<T>();
            if inc_cap > 0 && chunk_count == 0 {
                chunk_count = 1;
            }
            for _ in 0..chunk_count {
                self.chunks.push( Chunk::new( self.ppool ));
            }
            self.cap += inc_cap;
        }
    }

    /// Returns the number of elements in the pool, also referred to as its 'length'.
    #[inline]
    /// ```
    /// #[macro_use] extern crate indexed;
    /// use indexed::{Indexed,Pool};
    ///
    /// extrusive_indexed!{ Foo{ inner: &'static str }}
    ///
    /// let mut pool = pool!( Foo[ "a", "b", "c" ]);
    /// assert_eq!( pool.len(), 3 );
    /// ```
    #[inline]
    pub fn len( &self ) -> usize { self.len }
 
    /// Sets the length of a pool.
    ///
    /// This will explicitly set the size of the pool, without actually modifying its buffers,
    /// so it is up to the caller to ensure that the pool is actually the specified size.
    ///
    /// ```
    /// #[macro_use] extern crate indexed;
    /// use indexed::{Indexed,Pool};
    ///
    /// extrusive_indexed!{ Foo{ inner: char }}
    ///
    /// let mut pool = pool!( Foo[ 'r', 'u', 's', 't' ]);
    ///
    /// unsafe {
    ///     std::ptr::drop_in_place( &mut pool[3] );
    ///     pool.set_len( 3 );
    /// }
    ///
    /// assert_eq!( pool.len(), 3 );
    /// assert_eq!( pool.iter().map( |e| e.inner ).collect::<Vec<_>>(), vec!['r', 'u', 's'] );
    /// ```
    ///
    /// In this example, there is a memory leak since the memory locations
    /// owned by the first `Name` were not freed prior to the `set_len` call:
    ///
    /// ```
    /// #[macro_use] extern crate indexed;
    /// use indexed::{Indexed,Pool};
    ///
    /// static mut COUNT: usize = 0;
    ///
    /// struct Name { index: usize, text: String }
    ///
    /// impl_indexed!{ Name{ index: usize }}
    ///
    /// impl Drop for Name { fn drop( &mut self ) { unsafe{ COUNT += 1; }}}
    ///
    /// impl From<&'static str> for Name {
    ///     fn from( s: &'static str ) -> Self {
    ///         Name{ index: <Self as Indexed>::null(), text: s.to_string() }
    ///     }
    /// }
    ///
    /// let mut pool = pool!( Name[ "abc", "def", "g" ]);
    ///
    /// unsafe {
    ///     std::ptr::drop_in_place( &mut pool[2] );
    ///     std::ptr::drop_in_place( &mut pool[1] );
    ///     pool.set_len( 0 );
    /// }
    ///
    /// assert_eq!( unsafe{ COUNT }, 2 );
    /// ```
    /// In this example, the pool gets expanded from zero to four items without any memory allocations occurring,
    /// resulting in pool values of unallocated memory:
    ///
    /// ```
    /// #[macro_use] extern crate indexed;
    /// use indexed::{Indexed,Pool};
    ///
    /// extrusive_indexed!{ Foo{ inner: &'static str }}
    ///
    /// let mut pool = Pool::<Foo>::new();
    /// unsafe { pool.set_len( 3 ); }
    /// ```
    #[inline]
    pub unsafe fn set_len( &mut self, len: usize ) {
        self.len = len;
        let sublen = len % chunk_len::<T>();
        self.subidx = if sublen == 0 { chunk_len::<T>()-1 } else { sublen-1 };
    }

    /// Returns the number of elements the vector can hold without more allocating.
    ///
    /// Note: **the purpose of this method is not to avoid reallocation**, which could not happen at all, but to grow the buffer for next incomming `write()`s.
    #[inline]
    pub fn capacity( &self ) -> usize { self.cap }

    /// Returns the pool's `NonNull` pointer.
    ///
    /// # Examples
    ///
    /// ```
    /// #[macro_use] extern crate indexed;
    /// use indexed::{Indexed,Pool};
    ///
    /// extrusive_indexed!{ Foo{ inner: i32 }}
    ///
    /// let mut pool = Pool::<Foo>::new();
    /// let p = pool.non_null();
    ///
    /// assert_eq!( p, std::ptr::NonNull::new( Box::into_raw( pool )).unwrap() );
    /// ```
    pub fn non_null( &self ) -> NonNull<Self> { self.ppool }

    /// Obtains reference of the pool of an element.
    /// 
    /// # Examples
    /// 
    /// ```
    /// #[macro_use] extern crate indexed;
    /// use indexed::{Indexed,Pool};
    ///
    /// extrusive_indexed!{ Foo{ inner: usize }}
    ///
    /// let mut pool = Pool::<Foo>::new();
    ///
    /// for i in 0..1024 {
    ///     pool.push( i.into() );
    /// }
    ///
    /// for i in 0..1024 {
    ///     assert!( pool.non_null().as_ptr() as *const Pool<Foo> == pool[i].pool() );
    /// }
    /// ```
    pub fn pool( value: &T ) -> &Self {
        unsafe {
            let remainder = value.get_index() % chunk_len::<T>();
            let value = value as *const T;
            let off = ( chunk_len::<T>() - remainder ) as isize;
            let ppool = ptr::read( value.offset( off ) as *const PPool<T> );
            &*ppool.as_ptr()
        }
    }

    /// Obtains mutable reference of the pool from an element.
    /// 
    /// # Safety
    /// 
    /// This operation is marked unsafe because it obtains a mutable reference of the `Pool` from one of its immutable element,
    /// which may violate the memory safety rule "only one mutable reference, or none but multiple immutable references".
    /// 
    /// # Examples
    /// 
    /// ```
    /// #[macro_use] extern crate indexed;
    /// use indexed::{Indexed,Pool};
    ///
    /// extrusive_indexed!{ Foo{ inner: usize }}
    ///
    /// let mut pool = Pool::<Foo>::new();
    ///
    /// for i in 0..1024 {
    ///     pool.push( i.into() );
    /// }
    ///
    /// for i in 0..1024 {
    ///     assert_eq!( pool.non_null().as_ptr(),
    ///                 unsafe{ pool[i].pool_mut() as *mut Pool<Foo>});
    /// }
    /// ```
    pub unsafe fn pool_mut( value: &T ) -> &mut Self {
        let remainder = value.get_index() % chunk_len::<T>();
        let value = value as *const T;
        let off = ( chunk_len::<T>() - remainder ) as isize;
        let ppool = ptr::read( value.offset( off ) as *const PPool<T> );
        &mut *ppool.as_ptr()
    }

    /// Obtains `NonNull` pointer of the pool from an element.
    pub fn pool_non_null( value: &T ) -> NonNull<Self> { unsafe{ NonNull::new_unchecked( Self::pool_mut( value ))}}

    /// Returns the expected index for the next new element to be `push()`ed in.
    pub fn new_index( &self ) -> usize { self.len }

    /// Returns `true` if the pool contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// #[macro_use] extern crate indexed;
    /// use indexed::{Indexed,Pool};
    ///
    /// extrusive_indexed!{ Foo{ inner: &'static str }}
    ///
    /// let mut pool = Pool::new();
    /// assert!( pool.is_empty() );
    ///
    /// pool.push( Foo::from( "foo" ));
    /// assert!( !pool.is_empty() );
    /// ```
    pub fn is_empty( &self ) -> bool { self.len == 0 }

    /// Returns an iterator over the pool.
    ///
    /// # Examples
    /// ```
    /// #[macro_use] extern crate indexed;
    /// use indexed::{Indexed,Pool};
    ///
    /// extrusive_indexed!{ Foo{ inner: &'static str }}
    ///
    /// let mut pool = pool!( Foo[ "abc", "def", "g" ]);
    /// let mut iter = pool.iter();
    ///
    /// assert_eq!( iter.next().unwrap().inner, "abc" );
    /// assert_eq!( iter.next().unwrap().inner, "def" );
    /// assert_eq!( iter.next().unwrap().inner, "g"   );
    /// assert!( iter.next().is_none() );
    /// ```
    #[inline]
    pub fn iter( &self ) -> Iter<T> {
        let last = if self.chunks.is_empty() {(0,0)} else {( self.chunks.len()-1, self.subidx )};
        Iter{ pool: self, chunk_idx: 0, elem_idx: 0, last }
    }

    /// Returns an iterator that allows modifying each value.
    ///
    /// # Examples
    ///
    /// ```
    /// #[macro_use] extern crate indexed;
    /// use indexed::{Indexed,Pool};
    ///
    /// extrusive_indexed!{ Foo{ inner: i32 }}
    ///
    /// let mut pool = pool!( Foo[ 0, 1, 2 ]);
    ///
    /// pool.iter_mut().for_each( |elem| { elem.inner += 10; });
    ///
    /// assert_eq!( pool.iter().map( |e| e.inner ).collect::<Vec<_>>(), vec![ 10, 11, 12 ]);
    /// ```
    pub fn iter_mut( &mut self ) -> IterMut<T> {
        let last = if self.chunks.is_empty() {(0,0)} else {( self.chunks.len()-1, self.subidx )};
        IterMut{ pool: self, chunk_idx: 0, elem_idx: 0, last }
    }

    /// Returns a shared reference to the output at indexed location, without performing any bounds checking.
    pub unsafe fn get_unchecked( &self, index: usize ) -> &T {
        &self.chunks.get_unchecked( index / chunk_len::<T>() )[ index % chunk_len::<T>() ]
    }

    /// Returns a mutable reference to the output at indexed location, without performing any bounds checking.
    pub unsafe fn get_unchecked_mut( &mut self, index: usize ) -> &mut T {
        &mut self.chunks.get_unchecked_mut( index / chunk_len::<T>() )[ index % chunk_len::<T>() ]
    }

    fn check( len: usize, grow: fn(usize,usize) -> Option<usize>, additional: usize ) -> usize {
        let len = grow( len, additional ).expect( "the requested capacity should be less or equal to `usize::MAX`" );
        if mem::size_of::<usize>() < 8 && len > !0_isize as usize {
            panic!( "the requested capacity on 32/16 bit platform should be less or equal to `isize::MAX`" );
        }
        len
    }

    fn check_len( &self, grow: fn(usize,usize) -> Option<usize>, additional: usize ) -> usize { Self::check( self.len, grow, additional )}
}

impl<T:Indexed> Drop for Pool<T> {
    fn drop( &mut self ) {
        let len = self.chunks.len();
        if self.managed && len > 0 {
            for i in 0..len-1 {
                let chunk = unsafe{ self.chunks.get_unchecked_mut(i) };
                unsafe{ chunk.0.set_len( 0 ); }
                for j in 0..chunk_len::<T>() {
                    unsafe{ drop_in_place( &mut chunk[j] ); }
                }
            }
            unsafe {
                let last_chunk = self.chunks.get_unchecked_mut( len-1 );
                for j in 0..=self.subidx {
                    last_chunk.0.set_len( 0 );
                    drop_in_place( &mut last_chunk[ j ]);
                }
            }
        }
    }
}

impl<T:Indexed> ops::Index<usize> for Pool<T> {
    type Output = T;
    fn index( &self, index: usize ) -> &T {
        &self.chunks[ index / chunk_len::<T>() ][ index % chunk_len::<T>() ]
    }
}

impl<T:Indexed> ops::IndexMut<usize> for Pool<T> {
    fn index_mut( &mut self, index: usize ) -> &mut T {
        &mut self.chunks[ index / chunk_len::<T>() ][ index % chunk_len::<T>() ]
    }
}

/// Immutable pool iterator
///
/// This struct is created by the `iter` method.
pub struct Iter<'a, T:'a+Indexed> {
    pool      : &'a Pool<T>,
    chunk_idx : usize,
    elem_idx  : usize,
    last      : ( usize, usize ),
}

impl<'a, T:'a+Indexed> Iterator for Iter<'a,T> {
    type Item = &'a T;

    fn next( &mut self ) -> Option<&'a T> {
        if ( self.chunk_idx, self.elem_idx ) <= self.last {
            let chunk = unsafe{ self.pool.chunks.get_unchecked( self.chunk_idx )};
            let elem = &chunk[ self.elem_idx ];
            if self.elem_idx == chunk_len::<T>() {
                self.elem_idx = 0;
                self.chunk_idx += 1;
            } else {
                self.elem_idx += 1;
            }
            Some( elem )
        } else {
            None
        }
    }
}

/// Mutable pool iterator
///
/// This struct is created by the `iter_mut` method.
pub struct IterMut<'a, T:'a+Indexed> {
    pool      : &'a mut Pool<T>,
    chunk_idx : usize,
    elem_idx  : usize,
    last      : ( usize, usize ),
}

impl<'a, T:'a+Indexed> Iterator for IterMut<'a,T> {
    type Item = &'a mut T;

    fn next( &mut self ) -> Option<&'a mut T> {
        if ( self.chunk_idx, self.elem_idx ) <= self.last {
            let chunk = unsafe{ self.pool.chunks.get_unchecked_mut( self.chunk_idx )};
            let elem = &mut chunk[ self.elem_idx ];
            if self.elem_idx == chunk_len::<T>() {
                self.elem_idx = 0;
                self.chunk_idx += 1;
            } else {
                self.elem_idx += 1;
            }
            Some( unsafe{ transmute( elem )})
        } else {
            None
        }
    }
}

/// Creates a `Pool` containing the arguments. The element type of the pool must be given explicitly inside the macro, of which the arguments is able to be converted `into`.
///
/// The wrapped data can be accessed via `inner` field.
///
/// # Examples
///
/// ```
/// #[macro_use] extern crate indexed;
/// use indexed::{Indexed,Pool};
///
/// extrusive_indexed!{ Foo{ inner: &'static str }}
///
/// let mut pool = pool!( Foo[ "a", "b", "c" ]);
///
/// assert_eq!( pool[0].inner, "a" );
/// assert_eq!( pool[1].inner, "b" );
/// assert_eq!( pool[2].inner, "c" );
/// ```
#[macro_export]
macro_rules! pool {
    ( $ty:ty[ $($x:expr),* ] ) => {{
        let mut pool = $crate::Pool::<$ty>::new();
        $( pool.push( $x.into() ); )*
        pool
    }};
    ( $ty:ty[ $($x:expr,)* ] ) => { pool!( $ty[ $($x),* ])};
}

/// Implements `Indexed` for a given type, using a given field as index storage of a given type which can be converted from/to `usize` using `as`.
///
/// # Examples
///
/// ```
/// #[macro_use] extern crate indexed;
/// use indexed::{Indexed,Pool};
///
/// struct Name { id: u32, text: String };
///
/// impl_indexed!{ Name{ id: u32 }}
///
/// let mut _pool = Pool::<Name>::new();
/// ```
#[macro_export]
macro_rules! impl_indexed {
    ( $name:ident { $field:ident:$field_ty:ty } ) => {
        unsafe impl Indexed for $name {
            unsafe fn get_index( &self ) -> usize { self.$field as usize }
            unsafe fn set_index( &mut self, index: usize ) { self.$field = index as $field_ty; }
        }
    };
}

/// Defines a wrapper type of a given type and implements `Indexed` for the wrapper.
///
/// The wrapped data can be accessed via `inner` field.
///
/// # Examples
///
/// ```
/// #[macro_use] extern crate indexed;
/// use indexed::{Indexed,Pool};
///
/// extrusive_indexed!{ Foo{ inner: i32 }}
///
/// let mut pool = pool!( Foo[
///     Foo::from( 0 ),
///     Foo::from( 1 ),
///     Foo::from( 2 ),
/// ]);
///
/// pool.iter_mut().for_each( |foo| foo.inner += 10 );
/// assert_eq!( pool.iter().map( |e| e.inner ).collect::<Vec<_>>(), vec![ 10, 11, 12 ]);
/// ```
#[macro_export]
macro_rules! extrusive_indexed {
    ($vis:vis $outer:ident { inner: $inner:ty }) => {
        $vis struct $outer { index: usize, pub inner: $inner }
        unsafe impl Indexed for $outer {
            unsafe fn get_index( &self ) -> usize { self.index }
            unsafe fn set_index( &mut self, index: usize ) { self.index = index; }
        }
        impl From<$inner> for $outer {
            fn from( inner: $inner ) -> Self { $outer{ index: <Self as Indexed>::null(), inner }}
        }
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        unsafe impl Indexed for (usize,usize) {
            unsafe fn get_index( &self ) -> usize { self.0 }
            unsafe fn set_index( &mut self, index: usize )  { self.0 = index; }
        }

        let pool: Box<Pool<(usize,usize)>> = Pool::new();
        let addr: *mut Pool<_> = Box::into_raw( pool );
        let mut pool: Box<Pool<(usize,usize)>> = unsafe{ Box::from_raw( addr )};
        let mut ptrs = Vec::new();
        let ( a, b ) = ( 256_usize, 1024 );
        for i in 0..a {
            pool.push( (0,i) );
            ptrs.push( &pool[i] as *const _ );
        }
        for i in a..b {
            pool.push( (0,i) );
        }
        for i in 0..a {
            assert_eq!( ptrs[i], &pool[i] as *const _ );
            assert_eq!( pool[i].pool() as *const _, addr );
        }
        for i in a..b {
            assert_eq!( pool[i].pool() as *const _, addr );
        }
    }

    #[test]
    #[should_panic( expected = "ZSTs are not allowed to be the `Pool`'s element type." )]
    fn test_zst() {
        struct S;
        unsafe impl Indexed for S {
            unsafe fn get_index( &self ) -> usize { !0 }
            unsafe fn set_index( &mut self, _index: usize ) {}
        }
        let _pool = Pool::<S>::new();
    }
}
