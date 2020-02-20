// /*@
//   @ requires \valid(p);
//   @ requires \valid(q);
//   @
//   @ ensures *p == \old(*q);
//   @ ensures *q == \old(*p);
// */
// void swap(int *p, int *q) {
//     int tmp = *p;
//     *p = *q;
//     *q = tmp;
// }

/*@
  @ requires \valid(p);
  @ requires \valid(q);
  @ requires -1000 <= *p <= 10000;
  @ requires -1000 <= *q <= 10000;
  @
  @ ensures *p == \old(*q);
  @ ensures *q == \old(*p);
*/
void swap(int *p, int *q) {
    *p += *q;
    *q = *p - *q;
    *p = *p - *q;
}