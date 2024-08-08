

sig Staff {
  head: one Note
}

sig Note {
  pitch: one Int,
  next: lone Note
}

fact range {
  all n: Note | n.pitch = {0} or
                   n.pitch = {1} or
                  n.pitch = {2} or
                   n.pitch = {3} or
                   n.pitch = {4} or
                   n.pitch = {5} or
                  n.pitch = {6} or
                   n.pitch = {7} or
                   n.pitch = {8} or
                   n.pitch = {9} or
                  n.pitch = {10} or
                   n.pitch = {11} 
 
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

pred par5asc {
  no i: Note | (i.pitch = {0} and i.next.pitch = {7} ) or
                          (i.pitch = {1} and i.next.pitch = {8} ) or
                          (i.pitch = {2} and i.next.pitch = {9} ) or
                          (i.pitch = {3} and i.next.pitch = {10} ) or
                          (i.pitch = {4} and i.next.pitch = {11} ) or
                          (i.pitch = {5} and i.next.pitch = {0} ) or
                          (i.pitch = {6} and i.next.pitch = {1} ) or
                          (i.pitch = {7} and i.next.pitch = {2} ) or
                          (i.pitch = {8} and i.next.pitch = {3} ) or
                          (i.pitch = {9} and i.next.pitch = {4} ) or
                          (i.pitch = {10} and i.next.pitch = {5} ) or
                          (i.pitch = {11} and i.next.pitch = {6} )
}

pred par5des {
  no i: Note | 
                          (i.next.pitch = {0} and i.pitch = {7} ) or
                          (i.next.pitch = {1} and i.pitch = {8} ) or
                          (i.next.pitch = {2} and i.pitch = {9} ) or
                          (i.next.pitch = {3} and i.pitch = {10} ) or
                          (i.next.pitch = {4} and i.pitch = {11} ) or
                          (i.next.pitch = {5} and i.pitch = {0} ) or
                          (i.next.pitch = {6} and i.pitch = {1} ) or
                          (i.next.pitch = {7} and i.pitch = {2} ) or
                          (i.next.pitch = {8} and i.pitch = {3} ) or
                          (i.next.pitch = {9} and i.pitch = {4} ) or
                          (i.next.pitch = {10} and i.pitch = {5} ) or
                          (i.next.pitch = {11} and i.pitch = {6} ) 
}

pred A {
  all n: Note | n not in n.^next
}

fact allreachable {
   no n: Note, s: Staff | n not in s.head.*next
}

fact { #Note.pitch > 1}
fact { #Staff = 2}

fact {
 no n: Note, s1,s2: Staff | n in s1.head.*next and n in s2.head.*next and s1 != s2
}

fact { 
  no n: Note | n.pitch = n.next.pitch
}

pred noPar5 {
 par5des and par5asc
}


pred show{
  A and noPar5
}

run show for 5 Int, 8 Note, 2 Staff
