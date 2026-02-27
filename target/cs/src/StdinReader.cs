using System;
using System.IO;
using System.Text;

namespace StdinReader {
  
  public partial class __default {
    public static Std.Wrappers._IResult<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>> ReadStdin()
    {
      try {
        var content = new StringBuilder();
        string line;
        
        while ((line = Console.In.ReadLine()) != null) {
          content.AppendLine(line);
        }
        
        var result = Dafny.Sequence<Dafny.Rune>.UnicodeFromString(content.ToString());
        return Std.Wrappers.Result<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>.create_Success(result);
      } catch (Exception ex) {
        var errorMessage = Dafny.Sequence<Dafny.Rune>.UnicodeFromString($"Error reading from stdin: {ex.Message}");
        return Std.Wrappers.Result<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>.create_Failure(errorMessage);
      }
    }
  }
}
