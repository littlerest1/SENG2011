predicate Sorted(a: array?<int>,start:int,end:int)
   reads a;
   requires a != null
   requires 0 <= start < end <= a.Length
{
  forall j, k :: start <= j < k < end ==> a[j] <= a[k]
}

method BubbleSort(a:array?<int>)
  requires a != null;
  modifies a;
  requires a.Length > 0;
  ensures a.Length > 0;
  ensures Sorted(a,0,a.Length);
  ensures multiset(a[..]) == multiset(old(a[..]));  
{
    var n := a.Length; 
    var i := 0;
    while(i < n -1)
    invariant 0 <= i <= n-1;
    invariant multiset(a[..]) == multiset(old(a[..]));  
    invariant forall x :: n-i-1 < x < n ==> a[n-i-1] <= a[x]; 
    //invariant forall x :: 1 <= x <= i ==> a[x] <= a[n-i-1]; 
    invariant forall x,y::  n-i <= x < y < n ==> a[x] <= a[y]; 
    
    {
      var j := 0;
      while(j < n-i-1)
      invariant 0 <= j <= n-i-1;
      invariant multiset(a[..]) == multiset(old(a[..]));
      invariant i == old(i) && n == old(n);
      invariant forall x :: 0 <= x < j ==> a[j] >= a[x];
     //  invariant forall x :: n-i <= x < n ==> a[n-i-1] <= a[x];    
     // invariant forall x:: 2*j <= x < x + 1 < a.Length  ==> a[x] <= a[x+1];
      {
         if(a[j] > a[j+1]){
           a[j],a[j+1] := a[j+1],a[j];
         }
         j := j + 1;
      }
      i := i + 1;
    }
}

method Main()
{
   // do not change this code
   var a := new int[][6,2,0,6,3,5,0,4,1,6,0]; // testcase 1
   var msa := multiset(a[..]);

   BubbleSort(a);
   assert Sorted(a, 0, a.Length);
   var msa' := multiset(a[..]);
   assert msa==msa';

   var b := new int[][8,7];  // testcase 2
   BubbleSort(b);

   print a[..], b[..];
}