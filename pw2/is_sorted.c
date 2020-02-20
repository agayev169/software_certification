/*@
  @ requires \valid(arr+(0.. n - 1));
  @ requires n > 0;
  @
  @ behavior true_:
  @   assumes \forall int i; 1 <= i < n ==> arr[i] >= arr[i - 1];
  @   ensures \result == 1;
  @ behavior false_:
  @   assumes \exists int i; 1 <= i < n &&  arr[i] <  arr[i - 1];
  @   ensures \result == 0; 
*/
int is_sorted(int arr[], int n) {
    /*@
      @ loop invariant 1 <= i <= n;
      @ loop invariant \forall int j; 1 <= j < i ==> arr[j] >= arr[j - 1];
      @ loop   variant n - i;
    */
    for (int i = 1; i < n; ++i) {
        if (arr[i] < arr[i - 1]) return 0;
    }
    return 1;
}