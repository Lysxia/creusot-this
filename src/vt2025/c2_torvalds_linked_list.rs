use creusot_std::{ghost::perm::Perm, prelude::*};

pub struct Node {
    next: *const Node,
}

pub struct List {
    head: *const Node,
    perms: Ghost<Seq<Box<Perm<*const Node>>>>,
}

#[trusted]
pub unsafe fn remove_better(l: &mut List, toremove: *const Node) {
    let mut p = &mut l.head;
    while *p != toremove {
        p = &mut (unsafe { &mut *(*p as *mut Node) as &mut Node }).next;
    }
    *p = unsafe { &*toremove as &Node }.next;
}
