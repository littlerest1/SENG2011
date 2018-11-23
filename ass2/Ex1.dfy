
class Score{
  var highestScore: int;
   predicate Valid() // class invariant
   reads this;
  { highestScore >= 0 }
  constructor()
    ensures Valid();
    ensures highestScore == 0;
  {
    highestScore := 0;
  }
  
  method NewScore(s: int)returns(b: bool,current: int)
  modifies this;
  requires s >= 0 && Valid();
  ensures Valid();
  ensures ((s > old(highestScore)) ==> (b == true && current == highestScore == s)) && ((s <= old(highestScore)) ==> (b == false && current == old(highestScore) == highestScore));
  {
    if( s > highestScore){
      this.highestScore:= s;
      b:= true;
      current:= this.highestScore;
      return b,current;
    }
    else{
      current:= highestScore;
      b:= false;
      return b,current;
    }
  }
}

method TestScore(){
  var s := new Score();
  var s1 := 0;
  assert s1 == 0;
  var b,current := s.NewScore(s1);
  assert b == false && current == 0; 
  
  var s2 := 2;
  assert s2 == 2;
  var b1,current1 := s.NewScore(s2);
  assert b1 == true && current1 == 2;
  
  assert s1 == 0;
  var b2,current2 := s.NewScore(s1);
  assert b2 == false && current2 == 2;
  
  var s3 := 4;
  assert s3 == 4;
  var b3,current3 := s.NewScore(s3);
  assert b3 == true && current3 == 4;
  
  var b4,current4 := s.NewScore(s3);
  assert b4 == false && current4 == 4;
  
  var s4 := 6;
  var b5,current5 := s.NewScore(s4);
  assert b5 == true && current5 == 6;
  assert s.highestScore == 6;
}