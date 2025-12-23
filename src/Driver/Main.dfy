module B3 {
  import opened Std.Wrappers
  import opened Basics
  import Types
  import RawAst
  import Parser
  import Std.FileIO
  import SB = Std.Parsers.StringBuilders
  import Printer
  import Ast
  import Resolver
  import ResolvedPrinter
  import TypeChecker
  import StaticConsistency
  import Verifier
  import CLI = CommandLineOptions
  import StdinReader

  class B3CliSyntax extends CLI.Syntax<Verb> {
    constructor () {
      ToolName := "b3";
    }

    method GetVerbs() returns (verbs: seq<(string, Verb)>) {
      verbs := [
        ("parse", Parse),
        ("resolve", Resolve),
        ("verify", Verify)
      ];
    }

    function GetOptionInfo(name: string): CLI.OptionInfo {
      match name
      case "print" => CLI.OptionInfo.ArgumentCount(0)
      case "rprint" => CLI.OptionInfo.ArgumentCount(0)
      case "solver-log" => CLI.OptionInfo.ArgumentCount(0)
      case "solver-log-no-options" => CLI.OptionInfo.ArgumentCount(0)
      case "solver-failure" => CLI.OptionInfo.ArgumentCount(0)
      case "show-proof-obligations" => CLI.OptionInfo.ArgumentCount(0)
      case "print-incarnations" => CLI.OptionInfo.ArgumentCount(0)
      case "cvc5" => CLI.OptionInfo.ArgumentCount(0)
      case "z3" => CLI.OptionInfo.ArgumentCount(0)
      case "stdin" => CLI.OptionInfo.ArgumentCount(0)
      case _ => CLI.OptionInfo.Unknown
    }

    predicate IsStdinOption(name: string) {
      name == "stdin"
    }

    method GetOptionsHelp() returns (help: string) {
      help := "\nOptions:\n" +
              "  --print                      Print the raw AST\n" +
              "  --rprint                     Print the resolved AST\n" +
              "  --solver-log                 Show SMT solver log\n" +
              "  --solver-log-no-options      Show SMT solver log without options\n" +
              "  --solver-failure             Show solver failures\n" +
              "  --show-proof-obligations     Show proof obligations\n" +
              "  --print-incarnations         Print incarnations\n" +
              "  --z3                         Use Z3 solver (default)\n" +
              "  --cvc5                       Use CVC5 solver\n" +
              "  --stdin                      Read b3 program from stdin\n";
    }
  }

  datatype Verb = Parse | Resolve | Verify

  method Main(args: seq<string>) {
    var syntax := new B3CliSyntax();
    var cliResult := CLI.Parse(syntax, args);
    if cliResult.Failure? {
      print cliResult.error, "\n";
      return;
    }
    var cli := cliResult.value;
    
    var rawb3;
    if "stdin" in cli.options {
      // Read from stdin
      var r := ReadAndParseFromStdin();
      if r.IsFailure() {
        print r.error, "\n";
        return;
      }
      rawb3 := r.value;
    } else {
      // Read from file
      match |cli.files| {
        case 0 =>
          print "No files given on command line\n";
          return;
        case 1 =>
          var r := ReadAndParseProgram(cli.files[0]);
          if r.IsFailure() {
            print r.error, "\n";
            return;
          }
          rawb3 := r.value;
        case _ =>
          print "Only 1 filename is supported\n";
          return;
      }
    }

    if "print" in cli.options {
      Printer.Program(rawb3);
    }
    if cli.verb == Parse {
      return;
    }

    var resultResolver := ResolveAndTypeCheck(rawb3, cli);
    if resultResolver.IsFailure() {
      print resultResolver.error, "\n";
      return;
    }
    var b3 := resultResolver.value;
    if cli.verb == Resolve {
      return;
    }

    Verifier.Verify(b3, cli.options);
  }

  method ReadAndParseProgram(filename: string) returns (r: Result<RawAst.Program, string>) {
    var input :- FileIO.ReadUTF8FromFile(filename);
    var parseResult := SB.Apply(Parser.TopLevel, input);
    var b3 :- match parseResult {
      case ParseSuccess(value, remaining) => Success(value)
      case ParseFailure(_, _) => Failure(SB.FailureToString(input, parseResult))
    };
   return Success(b3);
  }

  method ReadAndParseFromStdin() returns (r: Result<RawAst.Program, string>) {
    var input :- StdinReader.ReadStdin();
    var parseResult := SB.Apply(Parser.TopLevel, input);
    var b3 :- match parseResult {
      case ParseSuccess(value, remaining) => Success(value)
      case ParseFailure(_, _) => Failure(SB.FailureToString(input, parseResult))
    };
    return Success(b3);
  }

  method ResolveAndTypeCheck(rawb3: RawAst.Program, cli: CLI.CliResult) returns (r: Result<Ast.Program, string>)
    ensures r.Success? ==> var b3 := r.value;
      b3.WellFormed() && TypeChecker.TypeCorrect(b3) && StaticConsistency.Consistent(b3)
  {
    var b3 :- Resolver.Resolve(rawb3);

    if "rprint" in cli.options {
      ResolvedPrinter.Program(b3);
    }


    var outcome := TypeChecker.TypeCheck(b3);
    if outcome.IsFailure() {
      return Failure(outcome.error);
    }

    outcome := StaticConsistency.CheckConsistent(b3);
    if outcome.IsFailure() {
      return Failure(outcome.error);
    }

    return Success(b3);
  }
}