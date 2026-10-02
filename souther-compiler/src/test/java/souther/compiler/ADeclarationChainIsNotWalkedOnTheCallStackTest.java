package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.test.OnItsOwnStack;

import java.util.StringJoiner;

/**
 * A module chains its declarations as long as it likes, and a pass that follows the chain on the
 * call stack answers a long one by running out of room — so what the module means would depend on
 * the stack of the thread that compiled it.
 *
 * <p>Each chain here is compiled on a thread with a small stack, at a length that ran out of it
 * while the walks over these declarations were recursive. What is asserted is only that it compiles.
 */
class ADeclarationChainIsNotWalkedOnTheCallStackTest {

    /** Small next to what the JVM gives a thread by default, so a walk as deep as the chain fails
     *  here on any platform this runs on. */
    private static final long STACK = 512L << 10;

    private static final int LINKS = 1000;

    @Test
    void aChainOfBehaviorsEachCallingTheOneBefore() {
        StringBuilder src = new StringBuilder("module chain exposing ( Out, b" + LINKS + " )\n\n"
                + "data Out = { o: Int }\n\n"
                + "behavior b1 : (n: Int) -> Out\n    constructs Out\nlet b1 (n) = Out { o = n }\n");
        for (int i = 2; i <= LINKS; i++) {
            src.append("behavior b").append(i).append(" : (n: Int) -> Out\n")
                    .append("let b").append(i).append(" (n) = b").append(i - 1).append("(n)\n");
        }
        assertCompilesOnASmallStack(src.toString());
    }

    /** Recursive helpers are left standing as methods rather than expanded, so the chain is one the
     *  call graph and what the module carries for its readers both follow. */
    @Test
    void aChainOfRecursiveHelpersEachCallingTheOneBefore() {
        StringBuilder src = new StringBuilder("module chain exposing ( f" + LINKS + " )\n\n"
                + "partial let f1 (n: Int) : Int = if n <= 0 then 0 else f1(n - 1)\n");
        for (int i = 2; i <= LINKS; i++) {
            src.append("partial let f").append(i).append(" (n: Int) : Int = if n <= 0 then f")
                    .append(i - 1).append("(n) else f").append(i).append("(n - 1)\n");
        }
        assertCompilesOnASmallStack(src.toString());
    }

    /** Each record holds the one before in a field, down to a number with a rule on it, so the rule
     *  is about a position as deep as the chain and what it is made of is a chain as long. */
    @Test
    void aChainOfRecordsEachHoldingTheOneBefore() {
        StringJoiner exposed = new StringJoiner(", ");
        StringBuilder decls = new StringBuilder("data T1 = Int\n    invariant value >= 1 && value <= 9\n");
        exposed.add("T1");
        for (int i = 2; i <= LINKS; i++) {
            exposed.add("T" + i);
            decls.append("data T").append(i).append(" = { x: T").append(i - 1).append(" }\n");
        }
        assertCompilesOnASmallStack("module chain exposing ( " + exposed + " )\n\n" + decls);
    }

    private static void assertCompilesOnASmallStack(String src) {
        OnItsOwnStack.ask("a compile on a small stack", STACK, () -> Compiler.compile(src));
    }
}
