/*@
  @ requires n > 1;
  @ requires \valid(a+(0..n - 1));
  @
  @ ensures \forall int i; 0 <= i < n ==> a[\result] <= a[i];
  @ ensures \exists int i; 0 <= i < n &&  a[\result] == a[i];
  @ ensures 0 <= \result < n; 
*/

int argmin(int a[], int n) {
    int index_min = 0;

    /*@
      @ loop invariant 1 <= i <= n;
      @ loop invariant \forall int j; 0 <= j < i ==> a[index_min] <= a[j];
      @ loop invariant \exists int j; 0 <= j < i &&  a[index_min] == a[j];
      @ loop invariant 0 <= index_min < n; 
      @ loop   variant n - i;
    */
    for (int i = 1; i < n; ++i) {
        if (a[i] < a[index_min])
            index_min = i;
    }

    return index_min;
}