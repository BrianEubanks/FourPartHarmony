//
// Brian Eubanks
// Problem Set 1
// FSM.als
//

abstract sig Staff {
 first: one Note
 //next: lone Note
 //,note: Int
}

one sig StaffS extends Staff {
 //first: one Note
 //next: lone Note
 //,note: Int
}

one sig StaffA extends Staff {
 //first: one Note
 //next: lone Note
 //,note: Int
}

one sig StaffT extends Staff {
 //first: one Note
 //next: lone Note
 //,note: Int
}

one sig StaffB extends Staff {
 //first: one Note
 //next: lone Note
 //,note: Int
}

sig Note {
  next: lone Note,
  index:  one Int
}

// All notes are in a Staff
fact Reachable {
  Note = Staff.first.*next
}

// Disjoint index
fact disjointindex{
  no n1: Note, n2: Note | n1 != n2 and n1.index = n2.index
}

// Disjoint Staff
fact disjointstaff {
  no n: Note, s: StaffS, a: StaffA, t: StaffT, b: StaffB | (n in s.first.*next and n in a.first.*next) or
                                                                     ( n in s.first.*next and n in t.first.*next) or
                                                                     ( n in s.first.*next and n in b.first.*next) or
                                                                     ( n in a.first.*next and n in t.first.*next) or
                                                                     ( n in a.first.*next and n in b.first.*next) or
                                                                     ( n in t.first.*next and n in b.first.*next)
}

// same size
fact samesize {
  //all n: Note, s: StaffS, a: StaffA | n in s.first.*next and n in a.first.*next
}

// Sequence of Notes are Acyclic
pred NotesAcylcic() {
  all n: Note | n not in n.^next
}

run {
    
  NotesAcylcic 

} for 8
