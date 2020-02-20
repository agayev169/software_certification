/*@
  @ requires \valid(a+(0..na - 1));
  @ requires \valid(b+(0..nb - 1));
  @ requires \valid(c+(0..na + nb - 1));
  @ requires na > 0;
  @ requires nb > 0;
  @ requires na + nb < 1000000000;
  @
  @ ensures \forall int i;  0 <= i < na ==> c[i] == a[i]; 
  @ ensures \forall int j; na <= j < nb ==> c[j] == b[j - na]; 
*/
void concat(int a[], int na, int b[], int nb, int c[]) {
    /*@
      @ loop invariant 0 <= i <= na;
      @ loop invariant \forall int j; 0 <= j < i ==> c[j] == a[j];
      @ loop   variant na - i;
    */
    for (int i = 0; i < na; ++i) {
        c[i] = a[i];
    }

    /*@
      @ loop invariant na <= i <= na + nb;
      @ loop invariant \forall int j;  0 <= j < na ==> c[j] == a[j];
      @ loop invariant \forall int j; na <= j < i  ==> c[j] == b[j - na];
      @ loop   variant na + nb - i;
    */
    for (int i = na; i < na + nb; ++i) {
        c[i] = b[i - na];
    }
}