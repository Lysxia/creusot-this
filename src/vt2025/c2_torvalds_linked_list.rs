use creusot_std::{ghost::perm::Perm, prelude::*, logic::such_that};

pub struct Node {
    next: *const Node,
}

pub struct List {
    head: *const Node,
    perms: Ghost<Seq<Box<Perm<*const Node>>>>,
}

impl Invariant for List {
    #[logic]
    fn invariant(self) -> bool {
        pearlite! {
            if self.perms.len() == 0 {
                self.head.is_null_logic()
            } else {
                self.head == *self.perms[0].ward()
                    && (forall<i> 0 <= i && i < self.perms.len() - 1 ==>
                        self.perms[i].val().next == *self.perms[i+1].ward())
                    && self.perms[self.perms.len() - 1].val().next.is_null_logic()
            }
        }
    }
}

impl List {
    #[logic]
    pub fn len_logic(self) -> Int {
        (*self.perms).len()
    }

    #[logic]
    pub fn elems(self) -> Seq<*const Node> {
        pearlite! {
            (*self.perms).map(|p: Box<Perm<*const Node>>| *p.ward())
        }
    }
}

#[trusted]
#[check(ghost)]
#[ensures(result.len() == seq.len())]
#[ensures((^seq).len() == seq.len())]
#[ensures(forall<i> 0 <= i && i < seq.len() ==> *result[i] == (*seq)[i])]
#[ensures(forall<i> 0 <= i && i < seq.len() ==> ^result[i] == (^seq)[i])]
fn seq_as_mut<T>(seq: &mut Seq<T>) -> Seq<&mut T> {
    todo!()
}

#[trusted]
#[check(ghost)]
#[ensures(result == l.concat(r))]
fn concat<T>(l: Seq<T>, r: Seq<T>) -> Seq<T> {
    todo!()
}

#[check(terminates)]
#[requires(l.len_logic() > 0)]
#[requires(exists<x: Int> 0 <= x && x < l.len_logic() && toremove == l.elems()[x])]
#[ensures({
    let x = such_that(|x: Int| 0 <= x && x < l.len_logic() && toremove == l.elems()[x]);
    l.elems() == l.elems()[..x].concat(l.elems()[x+1..])
})]
#[ensures(*result.ward() == toremove)]
pub unsafe fn remove_better(l: &mut List, toremove: *const Node) -> Ghost<Box<Perm<*const Node>>> {
    let _x = snapshot!{ such_that(|x: Int| 0 <= x && x < l.len_logic() && toremove == l.elems()[x]) };
    let mut perms = ghost! { std::mem::replace(&mut l.perms, Seq::new()).into_inner() };
    let _perms = snapshot! { perms };
    let mut right = ghost! { perms.split_off_ghost(*_x.into_ghost()) };
    let x_perm = ghost! { right.pop_front_ghost().unwrap() };

    let mut left_mut = ghost! { seq_as_mut(&mut *perms) };
    let mut _left_mut = snapshot! { *left_mut };

    let mut p = &mut l.head;
    let _head = snapshot! { p };
    #[variant(left_mut.len())]
    #[invariant(forall<i> 0 <= i && i < *_x - left_mut.len() - 1 ==> resolve(_left_mut[i]))]
    #[invariant(*left_mut == _left_mut[*_x - left_mut.len()..])]
    #[invariant(if *p != toremove {
            left_mut.len() > 0 && *p == *left_mut[0].ward()
        } else if *_x == 0 {
            ^*_head == ^p
        } else {
            (^_left_mut[*_x - 1]).val().next == ^p
        }
    )]
    while *p != toremove {
        let p_perm = ghost! { &mut **left_mut.pop_front_ghost().unwrap() };
        p = &mut (unsafe { Perm::as_mut(*p as *mut Node, p_perm) }).next;
    }
    *p = unsafe { Perm::as_ref(toremove, ghost! { &**x_perm }) }.next;
    ghost! { l.perms = ghost! { concat(perms.into_inner(), right.into_inner()) } };
    x_perm
}
