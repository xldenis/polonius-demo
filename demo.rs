// // fn x<'b, 'a : 'b>(a: &'a mut u32, b: &mut bool) -> &'a mut u32 {
// //   a
// // }

// // fn main () {}
// //

// // fn x() -> u32 {
// //   let mut x = 0;
// //   let a = &mut x;
// //   *a = 5;
// //   x
// // }
// //
// //
// fn borrow_in_tuple() {
//   let mut x = 0;
//   let mut y = 0;
//   let mut p = (&mut x, &mut y);

//   loop {
//     // invariant acc(p);
//     // invariant acc(p) -* acc(p)
//     p.0 = &mut * p.0;
//     *p.0 += 1;
//     continue
//   }
//   * p.1 = 5;
// }

fn aeneas() {
  let mut x = 0;
  let mut p = &mut x;

  loop {
    // invariant acc(p);
    // invariant acc(p) -* acc(p)
    p = &mut * p;
    *p += 1;
    continue
  }
}

// fn main() {

// }

// enum List {
//   Cons(i32, Box<List>),
//   Nil
// }

// fn all_zero(mut x : &mut List) {
//   // {_1: σ(0), }
//   // {_1: &mut loan(5) σ(11) }
//   while let List::Cons(i, tl) = x {
//     // invariant acc(x)
//     // invariant acc(x) -* acc(old(x ))
//     *i = 0;
              

//     x = tl;
//   }
//   // {_1: &mut loan(24) σ(40), _2: (), }
// }


// fn nth(mut x : &mut List, mut ix : usize) -> &mut i32 {
 
//   while let List::Cons(i, tl) = x {
//     // invariatn acc(x)
//     // invariant acc(x) -* old(acc(x))

//     if ix == 0 {
//       return i;
//     } 

//     ix -= 1;     
//     x = tl;
//   }
//   unreachable!()
//   // {_1: &mut loan(24) σ(40), _2: (), }
// }

// // fn swap<'a, 'b, T, U>(x : (&'a mut T, &'b mut U)) -> (&'b mut U, &'a mut T) {
// //   (x.1, x.0)
// // }
// 

fn main () {}