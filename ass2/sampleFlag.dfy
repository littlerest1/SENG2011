// sorts an unordered array consisting of the colours red, white and blue
// into the order of the Dutch National Flag: red, white then blue.

datatype Colour = RED | WHITE | BLUE

method FlagSort(flag: array?<Colour>) returns (white: int, blue: int)
requires flag!=null
ensures 0 <= white<=blue <= flag.Length
ensures forall i:: 0     <=i <white       ==> flag[i]==RED
ensures forall i:: white <=i <blue        ==> flag[i]==WHITE
ensures forall i:: blue  <=i <flag.Length ==> flag[i]==BLUE
ensures multiset(flag[..])== multiset(old(flag[..]))
modifies flag;
{
    var next := 0;
    white := 0;
    blue := flag.Length;    // colours between next and blue unsorted
    while (next != blue)    // when next==blue, no colours left to sort
    invariant 0 <= white<=next<=blue <= flag.Length
    invariant forall i:: 0    <=i<white       ==> flag[i]==RED
    invariant forall i:: white<=i<next        ==> flag[i]==WHITE
    invariant forall i:: blue <=i<flag.Length ==> flag[i]==BLUE
    invariant multiset(flag[..])== multiset(old(flag[..]))
    {
            match (flag[next])
            {
            case WHITE => next:=next+1;
            case BLUE  => blue:=blue-1;
                          flag[next], flag[blue] := flag[blue], flag[next];
            case RED   => flag[next], flag[white] := flag[white], flag[next];
                          next:=next+1;
                          white:=white+1;
            }
    }
}

method Main(){
  var a: array<Colour> := new Colour[6];
  a[0],a[1],a[2],a[3],a[4] := RED,WHITE,BLUE,RED,WHITE;
  var w,b := FlagSort(a);
  print w," ",b ,"\n";
  var i := 0;
  while(i < a.Length){
    print a[i];
    i := i + 1;
  }
  var x := 5/3;
  print "\n",x;
}