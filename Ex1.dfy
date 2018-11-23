method Tautology(){
  var p,q,r,s;
  assert (((p || q) ==> r) && (r ==> s)) ==>(!s ==>!p);
}