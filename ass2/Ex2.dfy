class actuator{
  ghost var switch:bool;
  ghost var circuit:bool;
  
  predicate Valid()
  reads this
  {(switch && !circuit) || (!switch && circuit)}

  constructor()
  ensures Valid();
  ensures !switch && circuit;
  {switch := false; circuit := true;}
  
  method StaySwitch()
  modifies this;
  requires Valid();
  requires switch && !circuit;
  ensures switch && !circuit;
  {}
  
  method StayCircuit()
  modifies this;
  requires Valid();
  requires circuit && !switch;
  ensures circuit && !switch;
  {}
  
  method GotoSwitch()
  modifies this;
  requires Valid();
  ensures Valid();
  requires !switch && circuit;
  ensures switch && !circuit;
  {switch := true; circuit := false;}
  
  method GotoCircuit()
  modifies this;
  requires Valid();
  ensures Valid();
  requires switch && !circuit;
  ensures !switch && circuit;
  {switch := false; circuit := true;}
}

method TestOk()
{
 var m := new actuator(); // we know it starts in B
 assert !m.switch && m.circuit;
 m.StayCircuit(); // stay in circuit open mode
 assert !m.switch && m.circuit;
// m.GotoCircuit(); ----- Bad behaviour since the switch is closed and circuit open in this stage
// m.StaySwitch(); ------ Bad behaviour as well,since the same reason as above

  
  m.GotoSwitch();  // now the switch is opened and circuit is closed
  assert m.switch && !m.circuit;
  m.StaySwitch(); // stay in circuit closed,switch open mode
  assert m.switch && !m.circuit;
  // m.GotoSwitch(); ----- Bad behaviour since the switch is opened and circuit close in this stage
  // m.StayCircuit(); ------ Bad behaviour as well,since the same reason as above

  m.GotoCircuit();// now the circuit is opened and switch is closed
  assert m.circuit && !m.switch;
  m.StayCircuit();
  assert m.circuit && !m.switch;
  // m.GotoCircuit(); ----- Bad behaviour since the switch is closed and circuit open in this stage
  // m.StaySwitch(); ------ Bad behaviour as well,since the same reason as above

}
