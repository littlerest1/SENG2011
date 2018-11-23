predicate Sorted(a: array?<int>,start:int,end:int)
   reads a;
   requires a != null
   requires 0 <= start < end <= a.Length
{
  forall j, k :: start <= j < k < end ==> a[j] <= a[k]
}

method InsertionSortShuffle(a:array?<int>)
  requires a != null;
  modifies a;
  requires a.Length > 0;
  ensures a.Length > 0;
  ensures Sorted(a,0,a.Length);
  ensures multiset(a[..]) == multiset(old(a[..]));  
{
  if(a.Length > 1){   
     var i := 1;
    
     while(i < a.Length)
      invariant 1 <= i <= a.Length;
      invariant forall x,y:: 0 <= x < y < i  ==> a[x] <= a[y]; 
      invariant multiset(a[..]) == multiset(old(a[..])); 
    {
      var key := a[i];
      var j := i - 1;
      
      a[i] := a[j];
      while(j >= 0 && a[j] > key)
        invariant -1 <= j < i;
        invariant forall x,y:: 0 <= x < y < i+1  ==> a[x] <= a[y]; 
        invariant forall x :: j < x < i ==> key < a[x];
        invariant multiset(a[..]) - multiset([a[j+1]]) + multiset([key]) ==  multiset(old(a[..]));
      {
        a[j+1] := a[j];
        j := j -1;
      }
      a[j+1] := key;
      i := i + 1;
    }
  }
}

method Main()
{
   // do not change this code
   var a := new int[][6,2,0,6,3,5,0,4,1,6,0]; // testcase 1
   var msa := multiset(a[..]);

   InsertionSortShuffle(a);
   assert Sorted(a, 0, a.Length);
   var msa' := multiset(a[..]);
   assert msa==msa';

   var b := new int[][8,7];  // testcase 2
   InsertionSortShuffle(b);

   print a[..], b[..];
}