predicate ColourSorted(flag:array?<Colour>)
  reads flag
  requires flag != null
{ forall i::0 <= i < i + 1 < flag.Length ==> (flag[i] == RED ==> (flag[i+1] == RED || flag[i+1] == BLUE)) || (flag[i] == BLUE ==> (flag[i+1] == BLUE || flag[i+1] == YELLOW))
 || (flag[i] == YELLOW ==> (flag[i+1] == YELLOW ||flag[i+1] == GREEN)) || (flag[i] == GREEN ==> flag[i+1] == GREEN)}

datatype Colour = RED| BLUE | YELLOW | GREEN

method FlagSort(flag:array?<Colour>)
requires flag != null;
ensures ColourSorted(flag);
ensures multiset(flag[..]) == multiset(old(flag[..]));
modifies flag;
{
 

  var next := 0;
  var blue := 0;
  var green := flag.Length;
  
  while(next != green)
  invariant 0 <= blue <= next <= green <= flag.Length;
  invariant forall i:: green <= i < flag.Length ==> flag[i]==GREEN;
  invariant forall i:: blue <= i < next ==> (flag[i] == BLUE || flag[i] == YELLOW);
  invariant forall i:: 0    <=i<blue       ==> flag[i]==RED;
  invariant multiset(flag[..]) == multiset(old(flag[..]));
  {
    match(flag[next]){
      case RED => flag[next],flag[blue] := flag[blue],flag[next];
                    blue := blue + 1;
                    next := next + 1;
      case BLUE => next := next + 1;
      case YELLOW => next := next + 1; 
      case GREEN => green := green - 1; 
                    flag[next],flag[green] := flag[green],flag[next];
    }
  }
  var yellow := blue;
  var n:= blue;
 
  if(blue < green ){
    while(n != green)
    invariant 0<= blue <= yellow <= n <= green <= flag.Length;
    invariant blue == old(blue) && green == old(green);
    invariant forall i:: blue <= i < green ==> (flag[i] == BLUE || flag[i] == YELLOW);
    invariant forall i:: 0    <=i<blue       ==> flag[i]==RED;
    invariant forall i:: blue<= i < yellow ==> flag[i] == BLUE;
    invariant forall i:: yellow<= i < n ==> flag[i] == YELLOW;
    invariant forall i:: green <= i < flag.Length ==> flag[i] == GREEN;
    invariant multiset(flag[..]) == multiset(old(flag[..]));
    {
      match(flag[n]){
        case RED => n := n + 1;
        case BLUE => flag[n],flag[yellow] := flag[yellow],flag[n];
                      yellow := yellow + 1;
                      n := n + 1;
        case YELLOW => n := n + 1; 
        case GREEN => n := n + 1;
      } 
    }
  } 
}

method Main(){
  var a: array<Colour> := new Colour[5];
  a[0],a[1],a[2],a[3],a[4] := YELLOW,YELLOW,GREEN,RED,BLUE;
  FlagSort(a);
  var i := 0;
  while(i < a.Length){
    print a[i];
    i := i + 1;
  }

}