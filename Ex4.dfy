method IncDec(x:int,y:int)returns(sum:int)
    ensures sum == x + y;
{
  var count :=0;
  var j := y;
  if(j < 0){
    j := -y;
  }
  sum := x;
  assert sum == x;
  assert y >= 0 ==> j ==y;
  assert y < 0 ==> j == -y;
  while count < j
     invariant 0 <= count <= j
     invariant y >= 0 ==> sum == x + count;
     invariant y <= 0 ==> sum == x - count;
     decreases j - count
  {
    if(y >= 0){
      sum := sum + 1;
    }
    else{
      sum := sum - 1;
    }
    count := count + 1;
  }
  assert y >= 0 ==> count == j == y;
  assert y < 0 ==> -count == -j == y; 
  assert y >= 0 ==> sum == x + count == x + j == x + y;
  assert y < 0 ==> sum == x - count == x + y;
}

method Main(){
   var sum := IncDec(5,15);
   assert sum == 20;
   
   sum := IncDec(5,-15);
   assert sum == -10;
   
   sum := IncDec(5,0);
   assert sum == 5;
   
   sum := IncDec(-5,15);
   assert sum == 10;
   
   sum := IncDec(-5,-15);
   assert sum == -20;
   
   sum := IncDec(-5,0);
   assert sum == -5;
}