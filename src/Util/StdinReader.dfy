module StdinReader {
  import opened Std.Wrappers

  export
    provides ReadStdin
    provides Wrappers

  @Axiom
  method {:extern} ReadStdin() returns (r: Result<string, string>)
    decreases *
}
