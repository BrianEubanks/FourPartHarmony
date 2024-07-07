//
// Brian Eubanks
// Problem Set 1
// FSM.als
//

sig Staff {
  head: one Note
}

sig Note {
 next: lone Note
 //,note: Int
}

// Four Staff
fact four {
  #Staff = 4
}

// All notes are in a Staff
fact Reachable {
  Note = Staff.head.*next
}

// All Staff Have the same number of notes
fact StaffSize {
  no n: Node, sa: Staff, sb: Staff | (sa != sb) and (#(n in sa.
}

// Sequence of Notes are Acyclic
pred NotesAcylcic() {
  all n: Note | n not in n.^next
}

// Notes are only in one Staff
pred NotesOneStaff() {
  no sa: Staff, sb: Staff | ((sa != sb) and (sa.head = sb.head))

}

pred NoteOne() {
  no n: Note, sa: Staff.head, sb: Staff.head |( (sa != sb) and (n in sa.*next) and (n in sb.*next))
}

run {
  NotesOneStaff and  
  NotesAcylcic  and
  NoteOne
} for 8
