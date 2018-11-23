predicate EOSorted(a: array?<int>)
      reads a
{
    (a == null) || (a!= null && forall j :: 0 <= j < j + 2 < a.Length ==> a[j] <= a[j+2])
} 
method Test(){
  var a: array<int> := new int[6];
  a[0],a[1],a[2],a[3],a[4],a[5] := 2,1,4,2,6,3;
  assert a[0] == 2 && a[1] == 1 && a[2] == 4 && a[3] == 2 && a[4] == 6 && a[5] == 3;
  assert EOSorted(a);
  
  var a1: array<int> := new int[2];
  a1[0],a1[1] := 1,2;
  assert a1[0] == 1 && a1[1] == 2;
  assert EOSorted(a1);
  
  var a2: array<int> := new int[2];
  a2[0],a2[1] := 2,1;
  assert a2[0] == 2 && a2[1] == 1;
  assert EOSorted(a2);
  
  var a3 :array?<int>:= null;
  assert a3 == null;
  assert EOSorted(a3);
  
  var a4 :array<int> := new int[][1,2,3,1];
  assert a4[0] == 1 && a4[1] ==2 && a4[2] == 3 && a4[3] == 1;
  assert !EOSorted(a4);
}