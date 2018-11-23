predicate just1(a:array?<int>,key:int)
   reads a
   requires a != null
   requires a.Length >= 1
{
  (exists k | 0 <= k < a.Length :: a[k] == key) && !(exists k,j | 0 <= k < j < a.Length :: a[k] == key && a[j] == key)
  // (exists k | 0 <= k < a.Length :: a[k] == key) && (((a[0] == key) && (forall k :: 1 <= k < a.Length ==> a[k] != key)) || (forall j,k,y :: 0 <= j < k < y < a.Length ==> (a[j] != key ==> a[k] == key ==>  a[y] != key))|| ((a[a.Length - 1] == key) && (forall k :: 0 <= k < (a.Length - 1) ==> a[k] != key)))
}
method Just1(a: array?<int>, key: int) returns (b: bool)
    requires a != null
    requires a.Length >= 1
    ensures just1(a,key) == b
{
   var i := 0;
   assert i == 0;
   while i < a.Length
    invariant 0 <= i <= a.Length;
    invariant !(exists k | 0 <= k < i :: a[k] == key)
    decreases (a.Length - i)
   {
     if(a[i] == key){
       var n := i + 1;
       assert n == i+1 && n > i;
       assert a[i] == key ==> exists k | 0 <= k <= i :: a[k] == key;
       if(n == a.Length){
         assert ((a[a.Length - 1] == key) && (forall k :: 0 <= k < (a.Length - 1) ==> a[k] != key));
         return true;
       }
       while n <  a.Length
         invariant a[i] == key;
         invariant i+1 <= n <= a.Length;
         invariant forall k :: (i + 1) <= k < n ==> a[k] != key;
         decreases (a.Length - n)
       {
         if(a[n] == key){
           assert forall k :: 0 <= k < i ==> a[k] != key && a[i] == key && !(forall j ::0<= i < j < a.Length ==> a[i] == key ==> a[j] != key);
           assert exists  k,y | 0 <= k < y < a.Length :: a[k] == key ==> a[y] == key;
           return false;
         }
          n := n + 1;
       }
       assert forall k :: (i + 1) <= k < a.Length ==> a[k] != key;
       assert a[i] == key && forall m :: 0 <= m < i ==> a[m] != key;
       return true;
     }
     i := i + 1;
   }
   assert i == a.Length;
   assert forall k :: 0<= k < a.Length ==> a[k] != key;
   assert !(exists k | 0 <= k < a.Length :: a[k] == key);
   return false;
}
method test(){
  var a1: array<int> := new int[][1,3,3,2,0,2,3,3,4];
  assert a1[0] == 1 && a1[1] == 3 && a1[2] == 3 && a1[3] == 2 && a1[4] == 0 && a1[5] == 2 && a1[6] == 3 && a1[7] == 3 && a1[8] == 4;
  assert just1(a1,1);
  assert just1(a1,0);
  assert just1(a1,4);
  assert !just1(a1,2);
  assert !just1(a1,3);
  assert !just1(a1,5);
}