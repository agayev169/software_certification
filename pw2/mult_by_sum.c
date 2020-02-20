/*@
  @ requires -10000 <= x <= 10000;
  @ requires      0 <= y <= 10000;
  @ 
  @ ensures \result == x * y;
*/
int mult(int x, int y) {

    int res = 0;

    /*@
      @ loop invariant 0 <= i <= y;
      @ loop invariant res == i * x;
      @ loop   variant y - i;
    */
    for (int i = 0; i < y; ++i) {
        res += x;
    }

    return res;
}