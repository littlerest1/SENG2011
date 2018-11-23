predicate Sorted(a: array <int >, low: int , high: int)
reads a
{
    forall i, j :: 0  <= low  <= i  <= j  < high <= a.Length ==> a[i]  <= a[j]
}

method BubbleSort(a: array <int>)
modifies a;
ensures Sorted(a, 0, a.Length);
ensures multiset(a[..]) == multiset(old(a[..]));
{
    var i := a.Length - 1;
    while(i > 0)
    invariant i < 0 ==> a.Length == 0;
    invariant Sorted(a, i, a.Length);
    invariant forall x, y :: 0  <= x  <= i < y < a.Length ==> a[x] <= a[y]; //VERY IMPORTANT!!
    invariant multiset(a[..]) == multiset(old(a[..]));
    {
        var j := 0;
        while (j < i)
        invariant 0 <= j <= i;
        invariant Sorted(a, i, a.Length);
        invariant forall x, y :: 0  <= x  <= i < y < a.Length ==> a[x] <= a[y];
        invariant forall k :: 0 <= k <= j ==> a[k] <= a[j];
        invariant multiset(a[..]) == multiset(old(a[..]));
        {
            if (a[j] > a[j+1]) {
                a[j], a[j+1] := a[j+1], a[j];
            }
            j := j + 1;
        }
        i := i - 1;
    }
}
