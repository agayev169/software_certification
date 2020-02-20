/*@
  @ requires n > 0;
  @ requires \valid(t+(0..n-1));
  @
  @ assigns \nothing;
  @ behavior true_:
  @   assumes \forall int i; 0 <= i < n ==> t[i] == 0;
  @   ensures \result == 1;
  @ behavior false_:
  @   assumes \exists int i; 0 <= i < n &&  t[i] != 0;
  @   ensures \result == 0;
*/
int all_zeros(int t[], int n) {
    /*@
      @ loop invariant 0 <= i <= n;
      @ loop invariant \forall int j; 0 <= j < i ==> t[j] == 0;
      @ loop variant   n - i;
    */
    for (int i = 0; i < n; ++i) {
        if (t[i] != 0) return 0;
    }
    return 1;
}