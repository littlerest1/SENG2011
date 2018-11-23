predicate clean1(a:array?<int>,key:int)
     reads a
{
  (a == null) || (forall k::0<= k < a.Length  ==> a[k] != key)
}

method IsClean(a: array?<int>, key: int) returns (clean: bool)
    ensures clean1(a,key) == clean;
{
    var index := 0;
    
    if(a==null){
     assert a == null;
     assert a == null;
     return true;
    }
    
    assert a!= null;
    assert index == 0;
    while index < a.Length
       invariant 0<=index<= a.Length;
       invariant forall k :: 0 <= k < index ==> a[k] != key;
       invariant !(exists k | 0 <= k < index :: a[k] == key);
	   decreases (a.Length - index)
    {
      if(a[index] == key){
        assert a[index] == key;
        assert exists k :: 0<= k <= index ==> a[k] == key;
        assert a != null ==> exists k :: 0<= k <= index ==> a[k] == key;
        return false;
      }
      index :=index+1;
    }
  //  assert a != null && clean == true;
    assert  !(exists k | 0 <= k < a.Length :: a[k] == key); 
    assert a != null && !(exists k :: 0<= k < a.Length ==> a[k] == key) ==> forall k :: 0 <= k < index ==> a[k] != key;
    return true;
}

method Test(){
  var a1: array<int> := new int[][1,2,2,3];
  assert a1[0] == 1 && a1[1] == 2 && a1[2] == 2 && a1[3] == 3;
  var clean := IsClean(a1,1);
  assert clean == false;
  clean:=IsClean(a1,2); assert clean == false;
  clean:=IsClean(a1,3); assert clean == false;
  clean:=IsClean(a1,4); assert clean == true;
  
  var a2:array<int> := new int[][1];
  assert a2[0] == 1;
  clean:=IsClean(a2,1); assert clean == false;
  clean:=IsClean(a2,2); assert clean == true;
  
  var a3 :array?<int>:= null;
  assert a3 == null;
  clean:=IsClean(a3,1); assert clean == true;
}