module DeclarationMarkers {
  // Objects that inherit from DeclarationMarker are used as declaration markers in RSolver.REngine, which allows
  // the verifier to keep track of which symbols have been passed to the solver.
  //
  // Note, the "{:termination false}" marker on the next line is no cause for alarms, since this trait does
  // not have any dynamically dispatched members. (So, really, Dafny ought not complain in the first place.)
  trait {:termination false} DeclarationMarker extends object {
  }
}