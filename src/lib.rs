// See the COPYRIGHT file at the top-level directory of this distribution.
// Licensed under MIT license <LICENSE-MIT or http://opensource.org/licenses/MIT>

//! This library provides a `Vec`-like, no reallocation collection named `indexed::Pool`.
//! The pool's reference can be obtained from one of its elements.
//! It can be used as a memory pool, and library users do not need to store/pass the pool's reference everywhere.
//! The elements can be linked to each other using indexes rather than pointers.
//!
//! # Example
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
//!     unsafe fn get( &self ) -> usize { self.index as usize }
//!     unsafe fn set( &mut self, index: usize ) { self.index = index as u32; }
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
#[cfg(not(feature="no_std"))] pub(crate) use std::mem::{self};
#[cfg(not(feature="no_std"))] pub(crate) use std::ops;
#[cfg(not(feature="no_std"))] pub(crate) use std::ptr::{self,NonNull};

#[cfg(feature="no_std")] extern crate alloc;
#[cfg(feature="no_std")] pub(crate) use self::alloc::boxed::Box;
#[cfg(feature="no_std")] pub(crate) use self::alloc::vec::Vec;
#[cfg(feature="no_std")] pub(crate) use core::fmt::{self,Debug};
#[cfg(feature="no_std")] pub(crate) use core::marker::PhantomData;
#[cfg(feature="no_std")] pub(crate) use core::mem::{self};
#[cfg(feature="no_std")] pub(crate) use core::ops;
#[cfg(feature="no_std")] pub(crate) use core::ptr::{self,NonNull};

/// Possible chunk sizes.
pub enum ChunkLen {
    B5 = 32, B6 = 64, B7 = 128, B8 = 256, B9 = 512, B10 = 1024, B11 = 2048, B12 = 4096, B13 = 8192, B14 = 16384, B15 = 32768, B16 = 65536,
}

fn chunk_len<T:Indexed>() -> usize { <T as Indexed>::chunk_len() as isize as usize }

/// Type of elements in the `Pool` must implement this trait.
/// Typically some integer field in the type must devote to storing the index in the pool, and it is not necessarily usize.
/// For example, an index can be stored in u32 if 4194304K is enough for anybody.
pub unsafe trait Indexed: Sized {
    /// Sets the underlying chunk size. The default is 256, and can be overrided by those values defined in `ChunkLen`.
    fn chunk_len() -> ChunkLen { ChunkLen::B8 }

    /// Defines which index value is for null. If the underlying storage for index is smaller than `usize`'s size, the library user should override this method and pick a smaller value, e.g `!0_u32` for index stored in `u32`.
    fn null() -> usize { !0_usize }

    /// Gets the element's index in the pool.
    unsafe fn get( &self ) -> usize;

    /// Sets the element's index in the pool. The library user is not expected to call it directly.
    unsafe fn set( &mut self, index: usize );

    /// Obtains reference of its pool.
    unsafe fn pool( &self ) -> &Pool<Self> { Pool::pool( self )}

    /// Obtains mutable reference of its pool.
    unsafe fn pool_mut( &self ) -> &mut Pool<Self> { Pool::pool_mut( self )}

    /// Appends an element to the back of its pool.
    fn pool_push( &self, value: Self ) -> usize { unsafe{ self.pool_mut().push( value )}}

    /// Overwrites a new value into its pool at given index without reading or dropping the old value.
    unsafe fn pool_write( &self, value: Self, index: usize ) { self.pool_mut().write( value, index ); }

    /// Reserves capacity for at least additional more elements to be inserted in the given Pool<T>. The collection may reserve more space because the increasing size must be multiple of underlying `chunk_len()`. After calling reserve, capacity will be greater than or equal to self.pool().new_index() + additional. Does nothing if capacity is already sufficient.
    fn pool_reserve( &self, additional: usize ) { unsafe{ self.pool_mut().reserve( additional ); }}
}

struct Chunk<T>( Vec<u8>, PhantomData<T> );

type PPool<T> = NonNull<Pool<T>>;

impl<T:Indexed> Chunk<T> {
    #[inline] fn data_size() -> usize { mem::size_of::<[T;1]>() * chunk_len::<T>() }

    #[inline] fn buffer_size() -> usize { Self::data_size() + mem::size_of::<PPool<T>>() }

    #[inline] fn as_ptr( &self ) -> *const T { self.0.as_ptr() as *const T }
    #[inline] fn as_mut_ptr( &mut self ) -> *mut T { self.0.as_mut_ptr() as *mut T }

    #[inline] fn data_ptr( &self, index: usize ) -> *const T { unsafe{( self.as_ptr() ).offset( index as isize )}}
    #[inline] fn data_mut_ptr( &mut self, index: usize ) -> *mut T { unsafe{( self.as_mut_ptr() ).offset( index as isize )}}

    #[inline] fn ppool( &self ) -> *const PPool<T> { self.data_ptr( chunk_len::<T>() ) as *const PPool<T> }

    #[inline] fn new( ppool: PPool<T> ) -> Self {
        unsafe {
            let mut buffer = Vec::<u8>::with_capacity( Self::buffer_size() );
            ptr::write( buffer.as_mut_ptr().offset( Self::data_size() as isize ) as *mut NonNull<_>, ppool );
            Chunk( buffer, PhantomData )
        }
    }

    #[inline] fn write( &mut self, value: T, index: usize ) {
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
#[derive(Debug)]
pub struct Pool<T:Indexed> {
    chunks  : Vec<Chunk<T>>,
    managed : bool,
    ppool   : PPool<T>,
    current : usize,
    total   : usize,
}

impl<T:Indexed> Pool<T> {
    /// Creates a new pool that owns its elements and drops them in destruction.
    pub fn new() -> Box<Self> { Self::new_pool( true )}

    /// Creates a new pool that does not own its elements. The library user should drops the elements manually to avoid memory leaks.
    pub fn new_unmanaged() -> Box<Self> { Self::new_pool( false )}

    fn new_pool( managed: bool ) -> Box<Self> {
        let pool = Box::new( Self {
            chunks  : Vec::new(),
            managed , 
            ppool  : NonNull::dangling(),
            current : chunk_len::<T>()-1,
            total   : 0,
        });
        unsafe {
            let pool = Box::into_raw( pool );
            let ppool = NonNull::new_unchecked( pool );
            let mut pool = Box::from_raw( pool );
            pool.ppool = ppool;
            pool
        }
    }

    /// Appends an element to the back of a pool.
    pub fn push( &mut self, mut value: T ) -> usize {
        self.current += 1;
        if self.current == chunk_len::<T>() {
            if self.total == self.chunks.len() * chunk_len::<T>() {
                self.chunks.push( Chunk::new( self.ppool ));
            }
            self.current = 0;
        }
        let total = self.total;
        unsafe{ value.set( total )};
        self.chunks.last_mut().unwrap().write( value, self.current );
        self.total += 1;
        total
    }

    /// Overwrites a new value into a pool at given index without reading or dropping the old value.
    pub unsafe fn write( &mut self, mut value: T, index: usize ) {
        value.set( index );
        self.chunks[ index / chunk_len::<T>() ].write( value, index % chunk_len::<T>() );
    }

    /// Reserves capacity for at least additional more elements to be inserted in the given Pool<T>. The collection may reserve more space because the increasing size must be multiple of underlying `chunk_len()`. After calling reserve, capacity will be greater than or equal to self.new_index() + additional. Does nothing if capacity is already sufficient.
    pub fn reserve( &mut self, additional: usize ) {
        for _ in 0 .. ( additional + self.current ) / chunk_len::<T>() {
            self.chunks.push( Chunk::new( self.ppool ));
        }
    }

    /// Obtains reference of the pool of an element.
    pub fn pool( value: &T ) -> &Self {
        unsafe {
            let remainder = value.get() % chunk_len::<T>();
            let value = value as *const T;
            let off = ( chunk_len::<T>() - remainder ) as isize;
            let ppool = ptr::read( value.offset( off ) as *const PPool<T> );
            &*ppool.as_ptr()
        }
    }

    /// Obtains mutable reference of the pool of an element.
    pub unsafe fn pool_mut( value: &T ) -> &mut Self {
        let remainder = value.get() % chunk_len::<T>();
        let value = value as *const T;
        let off = ( chunk_len::<T>() - remainder ) as isize;
        let ppool = ptr::read( value.offset( off ) as *const PPool<T> );
        &mut *ppool.as_ptr()
    }

    /// Returns the expected index for the next new element to be `push()`ed in.
    pub fn new_index( &self ) -> usize { self.total }
}

impl<T:Indexed> Drop for Pool<T> {
    fn drop( &mut self ) {
        let len = self.chunks.len();
        if self.managed && len > 0 {
            for i in 0..self.chunks.len()-1 {
                unsafe{ self.chunks[i].0.set_len( chunk_len::<T>() )};
            }
            unsafe{ self.chunks.last_mut().unwrap().0.set_len( self.current + 1 )};
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        unsafe impl Indexed for (usize,usize) {
            unsafe fn get( &self ) -> usize { self.0 }
            unsafe fn set( &mut self, index: usize )  { self.0 = index; }
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
            assert_eq!( unsafe{ pool[i].pool() } as *const _, addr );
        }
        for i in a..b {
            assert_eq!( unsafe{ pool[i].pool() } as *const _, addr );
        }
    }
}
