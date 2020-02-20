/*@
  @ requires n > 0;
  @ requires \valid(a+(0..n - 1));
  @ requires \valid(b+(0..n - 1));
  @ requires \valid(c+(0..n - 1));
  @ requires \forall int i; 0 <= i < n ==> -10000 <= a[i] <= 10000;
  @ requires \forall int i; 0 <= i < n ==> -10000 <= b[i] <= 10000;
  @
  @ ensures \forall int i; 0 <= i < n ==> c[i] == a[i] + b[i];
*/
void sum_array(int a[], int b[], int c[], int n) {
    /*@
      @ loop invariant 0 <= i <= n;
      @ loop invariant \forall int j; 0 <= j < i ==> c[j] == a[j] + b[j];
      @ loop   variant n - i; 
    */
    for (int i = 0; i < n; ++i) {
        c[i] = a[i] + b[i]; 
    }
}