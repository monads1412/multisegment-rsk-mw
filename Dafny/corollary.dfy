method Max(a: int, b: int) returns (m: int)
  ensures m >= a
  ensures m >= b
  ensures m == a || m == b
{
  if a >= b {
    m := a;
  } else {
    m := b;
  }
}

method Main()
{
  var x := 7;
  var y := 12;

  var m := Max(x, y);

  print "max = ", m, "\n";
}