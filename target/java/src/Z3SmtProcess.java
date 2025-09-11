package Z3SmtSolver;

import java.io.*;
import java.util.concurrent.TimeUnit;

public class Z3SmtProcess implements Smt.SmtProcess {
    private static final boolean DEBUG = false;
    private Process z3Process;
    private PrintWriter z3Input;
    private BufferedReader z3Output;
    private boolean isDisposed;

    public void log(String s) {
        if (DEBUG) {
            System.out.println(s);
        }
    }

    public Z3SmtProcess() {
        try {
            ProcessBuilder pb = new ProcessBuilder("z3", "-in", "-smt2");
            pb.redirectErrorStream(true);
            z3Process = pb.start();

            z3Input = new PrintWriter(z3Process.getOutputStream(), true);
            z3Output = new BufferedReader(new InputStreamReader(z3Process.getInputStream()));

            SendCmd("(set-option :produce-models true)");
            SendCmd("(set-logic ALL)");
            
            isDisposed = false;
        } catch (Exception ex) {
            System.out.println("Error initializing Z3: " + ex.getMessage());
            isDisposed = true;
        }
    }

    @Override
    public boolean Disposed() {
        return isDisposed;
    }

    @Override
    public dafny.DafnySequence<? extends dafny.CodePoint> SendCmd(dafny.DafnySequence<? extends dafny.CodePoint> cmdDafny) {
        String cmd = cmdDafny.verbatimString();
        String response = SendCmd(cmd);
        return dafny.DafnySequence.asUnicodeString(response);
    }

    public String SendCmd(String cmd) {
        try {
            if (isDisposed || z3Input == null || z3Output == null) {
                return "error: Z3 not initialized or disposed";
            }
            
            if ("(exit)".equals(cmd)) {
                isDisposed = true;
            }
            
            z3Input.println(cmd);
            z3Input.flush();
            log("Z3 << " + cmd);
            
            String response = readResponse(cmd);
            log("Z3 >> " + response);
            return response;
        } catch (Exception ex) {
            System.out.println("Error communicating with Z3: " + ex.getMessage());
            return "error: " + ex.getMessage();
        }
    }
    
    private String readResponse(String cmd) throws IOException {
        if ("(push)".equals(cmd) || "(pop)".equals(cmd) || cmd.startsWith("(assert ") || 
            cmd.startsWith("(set-option ") || cmd.startsWith("(set-logic ") ||
            "(exit)".equals(cmd) ||
            cmd.startsWith("(declare-fun") || cmd.startsWith("(declare-const") || cmd.startsWith("(declare-sort")) {
            return "success";
        }
        
        if ("(check-sat)".equals(cmd)) {
            return z3Output.readLine();
        }
        
        if ("(get-model)".equals(cmd)) {
            StringBuilder response = new StringBuilder();
            String line;
            int parenCount = 0;
            boolean started = false;
            
            while ((line = z3Output.readLine()) != null) {
                response.append(line).append("\n");
                
                for (char c : line.toCharArray()) {
                    if (c == '(') {
                        started = true;
                        parenCount++;
                    } else if (c == ')') {
                        parenCount--;
                    }
                }
                
                if (started && parenCount <= 0) {
                    break;
                }
            }
            
            return response.toString();
        }
        
        return z3Output.readLine();
    }
}
