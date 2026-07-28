package souther.compiler.query;

import souther.compiler.diag.Diagnostic;
import souther.compiler.meta.ModulePath;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

class ZzProbeTest {

    private static void compile(String label, Map<String, String> byId) {
        System.out.println("--- " + label);
        Compilation c = Compilation.ofDocuments(byId, Set.of(), ModulePath.EMPTY);
        try {
            Map<String, List<Diagnostic>> found = c.diagnostics();
            for (Map.Entry<String, List<Diagnostic>> e : found.entrySet()) {
                System.out.println("  === " + e.getKey());
                for (Diagnostic d : e.getValue()) {
                    System.out.println("    [" + d.code() + "/" + d.messageKey() + "] at " + d.pos()
                            + " args=" + (d.args() == null ? "null" : List.of(d.args())));
                }
            }
        } catch (RuntimeException | Error ex) {
            System.out.println("  !!! diagnostics threw " + ex.getClass().getName() + ": " + ex.getMessage());
        }
        try {
            System.out.println("  classes: " + c.classes().keySet());
        } catch (RuntimeException | Error ex) {
            System.out.println("  !!! classes threw " + ex.getClass().getName() + ": " + ex.getMessage());
        }
    }

    private static Map<String, String> one(String src) {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("a.sou", src);
        return byId;
    }

    @Test
    void probes() {
        compile("F2a emitted despite an error type in a body", one("""
                module m.a exposing ( f )

                behavior f : (n: Int) -> Int
                let f (n) = {
                    let x: Nowhere = n
                    x
                }
                """));

        compile("F2b example runs against that bytecode", one("""
                module m.a exposing ( f )

                behavior f : (n: Int) -> Int
                let f (n) = {
                    let x: Nowhere = n
                    x
                }

                example f
                  | (1) -> 1
                """));

        compile("F3a arithmetic operand cascade", one("""
                module m.a exposing ( A, f )

                data A = { n: Int }

                let twice (n: Int): Int = {
                    let x: Nowhere = n
                    x + x
                }

                behavior f : (a: A) -> Int
                let f (a) = twice(a.n)
                """));

        compile("F3b concat cascade", one("""
                module m.a exposing ( f )

                behavior f : (n: Int) -> String
                let f (n) = {
                    let x: Nowhere = n
                    "a" ++ x
                }
                """));

        Map<String, String> two = new LinkedHashMap<>();
        two.put("a.sou", """
                module m.a exposing ( B )

                import m.nope ( X )
                import m.good ( X )

                data B = { x: X }
                """);
        two.put("good.sou", """
                module m.good exposing ( X )

                data X = Int
                """);
        compile("F5 broken import line claims the name", two);

        Map<String, String> dup = new LinkedHashMap<>();
        dup.put("a.sou", """
                module m.a exposing ( B, mk )

                import m.dup ( A )

                data B = { a: A }

                behavior mk : (a: A) -> B
                    constructs B
                let mk (a) = B { a = a }

                example mk
                  | (A { n = 1 }) -> B { a = A { n = 1 } }
                """);
        dup.put("dup.sou", """
                module m.dup exposing ( A )

                data A = { n: Int }

                data A = { s: String }
                """);
        compile("F4 importer of a module with a duplicate", dup);

        compile("dup alone", one("""
                module m.a exposing ( A )

                data A = Int

                data A = String
                """));
    }
}
