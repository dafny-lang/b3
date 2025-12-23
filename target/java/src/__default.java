package StdinReader;

import java.io.*;
import java.nio.charset.StandardCharsets;

public class __default {
    public static Std.Wrappers.Result<dafny.DafnySequence<? extends dafny.CodePoint>, dafny.DafnySequence<? extends dafny.CodePoint>> ReadStdin()
    {
        try {
            BufferedReader reader = new BufferedReader(new InputStreamReader(System.in, StandardCharsets.UTF_8));
            StringBuilder content = new StringBuilder();
            String line;
            
            while ((line = reader.readLine()) != null) {
                content.append(line).append("\n");
            }
            
            dafny.DafnySequence<? extends dafny.CodePoint> result = dafny.DafnySequence.asUnicodeString(content.toString());
            return Std.Wrappers.Result.<dafny.DafnySequence<? extends dafny.CodePoint>, dafny.DafnySequence<? extends dafny.CodePoint>>create_Success(
                dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR),
                dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR),
                result);
        } catch (Exception ex) {
            String javaErrorMessage = "Error reading from stdin: " + ex.getMessage();
            dafny.DafnySequence<? extends dafny.CodePoint> errorMessage = dafny.DafnySequence.asUnicodeString(javaErrorMessage);
            return Std.Wrappers.Result.<dafny.DafnySequence<? extends dafny.CodePoint>, dafny.DafnySequence<? extends dafny.CodePoint>>create_Failure(
                dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR),
                dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR),
                errorMessage);
        }
    }
}
