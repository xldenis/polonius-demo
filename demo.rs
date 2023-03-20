// fn x<'b, 'a : 'b>(a: &'a mut u32, b: &mut bool) -> &'a mut u32 {
//   a
// }

// fn main () {}
//

fn x() -> u32 {
  let mut x = 0;
  let a = &mut x;
  *a = 5;
  x
}