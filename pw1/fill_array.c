/*@
  @ requires \valid(t+(0..n - 1));
  @ requires n > 0;
  @
  @ ensures \forall int i; 0 <= i < n ==> t[i] == val;
*/
void fill(int t[], int n, int val) {
    /*@
      @ loop invariant 0 <= i <= n;
      @ loop invariant \forall int j; 0 <= j < i ==> t[j] == val;
      @ loop variant n - i;
    */
    for (int i = 0; i < n; ++i) {
        t[i] = val;
    }
}