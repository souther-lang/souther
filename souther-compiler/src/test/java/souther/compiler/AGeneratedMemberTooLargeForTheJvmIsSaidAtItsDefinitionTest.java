package souther.compiler;

import souther.compiler.cst.SourceLayout;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.HumanRenderer;
import souther.compiler.diag.SourceContext;

import org.junit.jupiter.api.Test;

import java.util.Locale;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * How much a method holds and how many constants a class refers to are not known until it is
 * written, so these are not counted at the declaration the way argument slots are. The class file
 * writer refuses, and what it says names its own rule and the method it happened to be writing. It
 * is reported as the definition that was being emitted, which is the one the author can do something
 * about.
 *
 * <p>The widths here are the shapes that reach each limit first on this compiler, not thresholds the
 * JVM sets: what matters is that a small one is emitted and a large one is reported, so neither side
 * is pinned to a number the emitter could reasonably change.
 */
class AGeneratedMemberTooLargeForTheJvmIsSaidAtItsDefinitionTest {

    @Test
    void aBodyLongerThanOneMethodHoldsIsSaidAtTheBehavior() {
        assertDoesNotThrow(() -> Compiler.compile(behaviorOverAListOf(100)));

        String src = behaviorOverAListOf(8000);
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(src));
        assertEquals("E2102", e.code(), e.getMessage());
        assertTrue(e.getMessage().contains("f"), e.getMessage());
    }

    @Test
    void itSaysWhichGeneratedMethodAndHowFarPastTheLimit() {
        String src = behaviorOverAListOf(8000);
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(src));

        String said = new HumanRenderer(false).render(e.diagnostic(),
                new SourceContext("demo.sou", src, SourceLayout.of(src)), Locale.ENGLISH);
        assertTrue(said.contains("apply"), "the method it could not write: " + said);
        assertTrue(said.contains("65535"), "the limit it went past: " + said);
    }

    @Test
    void aClassNeedingMoreConstantsThanThePoolHoldsIsSaidAtTheBehavior() {
        String src = behaviorOverAListOf(40000);
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(src));
        assertEquals("E2103", e.code(), e.getMessage());
        assertTrue(e.getMessage().contains("f"), e.getMessage());
    }

    @Test
    void aRecursiveHelperTooLongForOneMethodIsSaidAtTheHelper() {
        String src = helperOverAListOf(8000);
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(src));
        assertEquals("E2102", e.code(), e.getMessage());
        assertTrue(e.getMessage().contains("spin"),
                "the helper, not the $Fns class the helpers share: " + e.getMessage());
    }

    /**
     * A text one constant does not hold is the same diagnostic whichever JDK runs this: one writer
     * says how long the text was and another does not, and one refuses it as a method is written and
     * another only as the class is. A value is emitted on the class the module's helpers share, so it
     * is said at the module, as a pool those helpers fill is.
     */
    @Test
    void aLiteralLongerThanOneConstantHoldsIsSaidTheSameOnEveryWriter() {
        assertDoesNotThrow(() -> Compiler.compile(aValueOfText("a".repeat(1000))));

        // Past the limit in modified UTF-8 and not in characters: each of these takes three bytes.
        String src = aValueOfText("あ".repeat(21846));
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(src));
        assertEquals("E2103", e.code(), e.getMessage());
        String said = new HumanRenderer(false).render(e.diagnostic(),
                new SourceContext("demo.sou", src, SourceLayout.of(src)), Locale.ENGLISH);
        assertTrue(e.getMessage().contains("`demo`"), e.getMessage());
        assertTrue(said.contains("65535"), "the limit it went past: " + said);
        assertFalse(said.contains("65538"), "not how far past, which not every writer says: " + said);
    }

    @Test
    void aDeclarationWhoseSourceIsLongerThanOneConstantHoldsIsSaidAtTheDeclaration() {
        // Each rule is short and a construction checks them all, so what grows is the text the
        // declaration is carried as.
        StringBuilder src = new StringBuilder("module demo exposing ( Code )\n\ndata Code = String\n");
        for (int i = 0; i < 120; i++) {
            src.append("    invariant String.length(value) <= ").append(1000 + i).append(" // ")
                    .append("x".repeat(600)).append('\n');
        }
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compile(src.toString()));
        assertEquals("E2103", e.code(), e.getMessage());
        assertTrue(e.getMessage().contains("`Code`"), e.getMessage());
    }

    @Test
    void aHeaderLongerThanOneConstantHoldsIsSaidAtTheModule() {
        // Few declarations with long names: what is measured is the header's text, and a
        // declaration costs the compile far more than the length of its name does.
        String longName = "T" + "x".repeat(400);
        StringBuilder src = new StringBuilder("module demo exposing ( ");
        int names = 170;
        for (int i = 0; i < names; i++) {
            src.append(i == 0 ? "" : ", ").append(longName).append(i);
        }
        src.append(" )\n\n");
        for (int i = 0; i < names; i++) {
            src.append("data ").append(longName).append(i).append(" = Int\n");
        }
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compile(src.toString()));
        assertEquals("E2103", e.code(), e.getMessage());
        assertTrue(e.getMessage().contains("`demo`"), e.getMessage());
    }

    private static String aValueOfText(String text) {
        return "module demo exposing ( greeting )\n\nlet greeting : String = \"" + text + "\"\n";
    }

    private static String listOf(int n) {
        return "[" + IntStream.range(0, n).mapToObj(String::valueOf)
                .collect(Collectors.joining(", ")) + "]";
    }

    private static String behaviorOverAListOf(int n) {
        return "module demo\n\ndata Out = { n: Int }\n\nbehavior f : (n: Int) -> Out\n"
                + "    constructs Out\nlet f (n) = Out { n = List.sum(" + listOf(n) + ") }\n";
    }

    private static String helperOverAListOf(int n) {
        return "module demo\n\ndata Out = { n: Int }\n\n"
                + "partial let spin (n: Int): Int =\n"
                + "    if n == 0 then List.sum(" + listOf(n) + ") else spin(n - 1)\n\n"
                + "behavior f : (n: Int) -> Out\n    constructs Out\n"
                + "let f (n) = Out { n = spin(n) }\n";
    }
}
