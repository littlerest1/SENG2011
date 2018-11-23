class DishWasher{
  ghost var Load :int;
  ghost var Unload :bool;
  ghost var Detergent :bool;
  ghost var Clean :bool;
  
  predicate Valid()
  reads this;
  {(Load < 10 && !Unload) || (Load == 10 && Unload)}
  
  //Initially it has 10 dishes capacity for load
  constructor()
  ensures Valid();
  ensures Unload && Load == 10 && !Detergent && !Clean;
  {Unload := true; Load := 10; Detergent := false;Clean := false;}
  
  method LoadDish(num:int)
  modifies this;
  requires num > 0;
  requires Valid();ensures Valid();
  ensures (num >= old(Load) ==> Load == 0) && (num < old(Load) ==> Load == old(Load) - num);
  ensures !Unload && Detergent == old(Detergent) && !Clean;
  { 
     if(Load > num){
       Load := Load - num;
     }
     else{
       Load := 0;
     }
     Unload := false;
     Clean:=false;
 }
  
  method AddDtgt()
  modifies this;
  requires Valid();ensures Valid();
  ensures Detergent && Load == old(Load) && Unload == old(Unload) && Clean == old(Clean);
  { Detergent := true;}
  
  method Wash()
  modifies this;
  requires Valid();ensures Valid();
  requires Load < 10 && Detergent && !Unload;
  ensures Load == old(Load) && !Detergent && Unload == old(Unload) && Clean;
  {Detergent := false;Clean := true;}
  
  method UnloadDish()
  modifies this;
  requires Valid();ensures Valid();
  requires Load  < 10 && !Unload && Clean;
  ensures Load == 10 && Unload && Detergent == old(Detergent) && Clean == old(Clean);
  { Load := 10;Unload := true;}  
}

method TestMachine()
{
  //Test case 1:load,add,wash,unload;
  var m := new DishWasher();
  assert m.Load == 10 && !m.Detergent && m.Unload && !m.Clean;
  m.LoadDish(10);
  assert m.Load == 0 && !m.Detergent && !m.Unload && !m.Clean;
  m.AddDtgt();
  assert m.Load == 0 && m.Detergent && !m.Unload && !m.Clean;
  m.Wash();
  assert m.Load == 0 && !m.Detergent && !m.Unload && m.Clean;
  m.UnloadDish();
  assert m.Load == 10 && !m.Detergent && m.Unload && m.Clean;
  
  //Test case 2:Add,Load,wash,unload;
  var k := new DishWasher();
  assert k.Load == 10 && !k.Detergent && k.Unload && !k.Clean;
  k.AddDtgt();
  assert k.Load == 10 && k.Detergent && k.Unload && !k.Clean;
  k.LoadDish(5);
  assert k.Load == 5 && k.Detergent && !k.Unload && !k.Clean;
  k.Wash();
  assert k.Load == 5 && !k.Detergent && !k.Unload && k.Clean;
  k.UnloadDish();
  assert k.Load == 10 && !k.Detergent && k.Unload && k.Clean;
  
  //Test case 3:Load,add,wash,add,unload,load,wash,unload
  var i := new DishWasher();
  assert i.Load == 10 && !i.Detergent && i.Unload && !i.Clean;
  i.LoadDish(6);
  assert i.Load == 4 && !i.Detergent && !i.Unload && !i.Clean;
  i.AddDtgt();
  assert i.Load == 4 && i.Detergent && !i.Unload && !i.Clean;
  i.Wash();
  assert i.Load == 4 && !i.Detergent && !i.Unload && i.Clean;
  i.AddDtgt();
  assert i.Load == 4 && i.Detergent && !i.Unload && i.Clean;
  i.UnloadDish();
  assert i.Load == 10 && i.Detergent && i.Unload && i.Clean;
  i.LoadDish(8);
  assert i.Load == 2 && i.Detergent && !i.Unload && !i.Clean;
  i.Wash();
  assert i.Load == 2 && !i.Detergent && !i.Unload && i.Clean;
  i.UnloadDish();
  assert i.Load == 10 && !i.Detergent && i.Unload && i.Clean;
  
  //Test case 4:Load,add,wash,add,wash,unload;
  var j := new DishWasher();
  assert j.Load == 10 && !j.Detergent && j.Unload && !j.Clean;
  j.LoadDish(12);
  assert j.Load == 0 && !j.Detergent && !j.Unload && !j.Clean;
  j.AddDtgt();
  assert j.Load == 0 && j.Detergent && !j.Unload && !j.Clean;
  j.Wash();
  assert j.Load == 0&& !j.Detergent && !j.Unload && j.Clean;
  j.AddDtgt();
  assert j.Load == 0 && j.Detergent && !j.Unload && j.Clean;
  j.Wash();
  assert j.Load == 0 && !j.Detergent && !j.Unload && j.Clean;
  j.UnloadDish();
  assert j.Load == 10 && !j.Detergent && j.Unload && j.Clean;
  
  //Test case 5:load,load,load,add,add,wash,unload;
  var n := new DishWasher();
  assert n.Load == 10 && !n.Detergent && n.Unload && !n.Clean;
  n.LoadDish(2);
  assert n.Load == 8 && !n.Detergent && !n.Unload && !n.Clean;
  n.LoadDish(3);
  assert n.Load == 5 && !n.Detergent && !n.Unload && !n.Clean;
  n.LoadDish(4);
  assert n.Load == 1 && !n.Detergent && !n.Unload && !n.Clean;
  n.AddDtgt();
  assert n.Load == 1 && n.Detergent && !n.Unload && !n.Clean;
  n.AddDtgt();
  assert n.Load == 1 && n.Detergent && !n.Unload && !n.Clean;
  n.Wash();
  assert n.Load == 1 && !n.Detergent && !n.Unload && n.Clean;
  n.UnloadDish();
  assert n.Load == 10 && !n.Detergent && n.Unload && n.Clean;
}
