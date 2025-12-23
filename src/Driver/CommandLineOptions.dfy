module CommandLineOptions {
  import opened Std.Wrappers
  import opened Basics

  export
    reveals Syntax, OptionInfo, CliResult, CliOptions
    provides Syntax.ToolName, Syntax.GetVerbs, Syntax.GetOptionInfo
    provides Parse
    provides Wrappers

  trait {:termination false} Syntax<Verb> {
    const ToolName: string

    method GetVerbs() returns (verbs: seq<(string, Verb)>)

    function GetOptionInfo(name: string): OptionInfo

    method GetOptionsHelp() returns (help: string)
  }

  datatype OptionInfo =
    | Unknown
    | ArgumentCount(n: nat)

  type CliOptions = map<string, seq<string>>

  datatype CliResult<Verb> = CliResult(verb: Verb, options: CliOptions, files: seq<string>)

  method Parse<Verb>(syntax: Syntax<Verb>, args: seq<string>) returns (result: Result<CliResult<Verb>, string>) {
    // Check for --help at the top level (b3 --help)
    if |args| >= 2 && args[1] == "--help" {
      var verbs := syntax.GetVerbs();
      var helpMsg := BuildGeneralHelp(syntax, verbs);
      return Failure(helpMsg);
    }
    
    if |args| < 2 {
      var verbs := syntax.GetVerbs();
      var helpMsg := BuildGeneralHelp(syntax, verbs);
      return Failure(helpMsg);
    }

    var verbs := syntax.GetVerbs();
    var verb;
    if i :| 0 <= i < |verbs| && verbs[i].0 == args[1] {
      verb := verbs[i].1;
    } else {
      var verbList := BuildVerbList(verbs, ", ");
      return Failure("Unrecognized verb: " + args[1] + "\n\nAvailable verbs: " + verbList);
    }

    // Check for --help after verb (b3 verify --help)
    if |args| >= 3 && args[2] == "--help" {
      var helpMsg := BuildVerbHelp(syntax, args[1]);
      return Failure(helpMsg);
    }

    var options := map[];
    var files := [];
    var i := 2;
    while i < |args| {
      var arg := args[i];
      if "--" <= arg {
        var optionName := arg[2..];
        var info := syntax.GetOptionInfo(optionName);
        if info == Unknown {
          var optionsHelp := syntax.GetOptionsHelp();
          return Failure("Unknown option: --" + optionName + optionsHelp);
        } else if |args| < i + 1 + info.n {
          return Failure("Option --" + optionName + " requires " + Int2String(info.n) + " arguments, but only " + Int2String(|args| - 1) + " are given");
        } else if optionName in options {
          return Failure("Option --" + optionName + " is given more than once");
        }
        options := options[optionName := args[i..i + info.n]];
        i := i + 1 + info.n;
      } else {
        files := files + [arg];
        i := i + 1;
      }
    }

    return Success(CliResult(verb, options, files));
  }

  method BuildGeneralHelp<Verb>(syntax: Syntax<Verb>, verbs: seq<(string, Verb)>) returns (help: string) {
    var verbListMultiline := BuildVerbList(verbs, "\n  ");
    help := "Usage: " + syntax.ToolName + " <verb> [options] <filename>\n\n" +
            "Verbs:\n  " + verbListMultiline + "\n\n" +
            "Example: " + syntax.ToolName + " verify program.b3\n\n" +
            "For verb-specific options, use: " + syntax.ToolName + " <verb> --help";
  }

  method BuildVerbHelp<Verb>(syntax: Syntax<Verb>, verb: string) returns (help: string) {
    var optionsHelp := syntax.GetOptionsHelp();
    help := "Usage: " + syntax.ToolName + " " + verb + " [options] <filename>" + optionsHelp;
  }

  method BuildVerbList<Verb>(verbs: seq<(string, Verb)>, separator: string) returns (list: string) {
    list := "";
    for i := 0 to |verbs| {
      if i > 0 {
        list := list + separator;
      }
      list := list + verbs[i].0;
    }
  }
}