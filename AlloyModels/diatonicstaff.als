

one sig Staff {
  head: one Note
}



sig Note {
  s: one Int,
  a: one Int,
  t: one Int,
  b: one Int,
  next: lone Note
}

pred irange(n:Int) {
   n = {0} or
                   n = {1} or
                  n = {2} or
                   n = {3} or
                   n = {4} or
                   n = {5} or
                   n = {6} or
                   n = {7} or
                   n = {8}/* or
                   n = {9} or
                  n = {10} or
                   n = {11} */
// Diatonic comment
}

fact prange {
  all n: Note | irange[n.s] and irange[n.a] and irange[n.t] and irange[n.b]
}



/*
fact {
  one n: Note | n.next = none
}*/

/*
pred par5 {
  some i: Interval | (i.note1 = {0} and i.note2 = {7} ) or
                          (i.note1 = {1} and i.note2 = {8} ) or
                          (i.note1 = {2} and i.note2 = {9} ) or
                          (i.note1 = {3} and i.note2 = {10} ) or
                          (i.note1 = {4} and i.note2 = {11} ) or
                          (i.note1 = {5} and i.note2 = {0} ) or
                          (i.note1 = {6} and i.note2 = {1} ) or
                          (i.note1 = {7} and i.note2 = {2} ) or
                          (i.note1 = {8} and i.note2 = {3} ) or
                          (i.note1 = {9} and i.note2 = {4} ) or
                          (i.note1 = {10} and i.note2 = {5} ) or
                          (i.note1 = {11} and i.note2 = {6} )
}
*/



pred ser5[n1,n2: Int] {
  (n1 = {0} and n2 = {7} ) or
                          (n1 = {1} and n2 = {8} ) or
                          (n1 = {2} and n2 = {9} ) or
                          (n1 = {3} and n2 = {10} ) or
                          (n1 = {4} and n2 = {11} ) or
                          (n1 = {5} and n2 = {0} ) or
                          (n1 = {6} and n2 = {1} ) or
                          (n1 = {7} and n2 = {2} ) or
                          (n1 = {8} and n2 = {3} ) or
                          (n1 = {9} and n2 = {4} ) or
                          (n1 = {10} and n2 = {5} ) or
                          (n1 = {11} and n2 = {6} ) 
}


pred par5 {
  some n1,n2: Note | n1 !=n2 and n1.next = n2 and 
                             ( (ser5[n1.s,n1.a] and ser5[n2.s,n2.a]) or
                               (ser5[n1.s,n1.t] and ser5[n2.s,n2.t]) or
                               (ser5[n1.t,n1.a] and ser5[n2.t,n2.a]) or
                               (ser5[n1.s,n1.b] and ser5[n2.s,n2.b]) or
                               (ser5[n1.b,n1.t] and ser5[n2.b,n2.t]) or
                               (ser5[n1.b,n1.a] and ser5[n2.b,n2.a]) )
}


pred A {
  all n: Note | n not in n.^next
}

fact allreachable {
   no n: Note, s: Staff | n not in s.head.*next
}

fact { #Note.s > 1}
//fact { #Staff = 2}

fact {
 no n: Note, s1,s2: Staff | n in s1.head.*next and n in s2.head.*next and s1 != s2
}

fact { 
  no n: Note | n.s = n.next.s
}



pred show{
  A and  !par5
}

run show for 5 Int, exactly 4 Note
