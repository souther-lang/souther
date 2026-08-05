package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.frontend.CstFrontend;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Ast;

import java.nio.file.Path;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A name is canonical whichever door it comes in by.
 *
 * <p>Two spellings Unicode calls canonically equivalent are one text, and a name is compared by its
 * code units wherever it is looked up — a declaration against a reference, a case against a wire tag,
 * a `--behavior` argument against what the module declares. So the two have to be one name, and this
 * walks the doors rather than the code.
 *
 * <p>They come through one function ({@code Reserved.name}) because doing it per door is how this
 * went wrong twice — once with the wire tag canonicalized and the name it came from not, and once
 * with the identifier canonicalized and four other doors not.
 *
 * <p>What this covers: an identifier, a type variable, the module name a header-less source is given,
 * and the file stem the CLI derives one from. What it does not: the identifiers an invocation names
 * on the command line ({@code run --behavior}, {@code examples --module}, {@code examples
 * --behavior}). Those go through the same function and are one line each, but nothing here drives
 * them, so a door that stopped using it would not be caught. Said rather than implied, because a
 * comment claiming a door is walked is worse than no comment at all.
 */
class ANameIsCanonicalWhereverItEntersTest {

    /** か + a combining voiced sound mark. */
    private static final String NFD = "\u304b\u3099";
    /** The same kana as one code point. */
    private static final String NFC = "\u304c";

    private static final String HEADERLESS = """
            data Out = Int

            behavior greet : (n: Int) -> Out constructs Out

            let greet (n) = Out(n)
            """;

    @Test
    void theTwoSpellingsAreDifferentStrings() {
        // The premise, so nothing below can pass by the two being equal already.
        assertEquals(NFC, Reserved.name(NFD));
        assertTrue(!NFD.equals(NFC));
    }

    @Test
    void aModuleNameGivenToAHeaderlessSource() {
        assertEquals(NFC, CstFrontend.parse(HEADERLESS, NFD).name(),
                "the caller's name for a header-less source is a name from outside");
    }

    @Test
    void aModuleNameTheCliDerivesFromAFileStem() {
        assertEquals(NFC, Runner.moduleName(Path.of(NFD + ".sou")));
        assertEquals(NFC, Runner.moduleName(Path.of(NFC + ".sou")));
    }

    @Test
    void aDecomposedStemIsNotRejectedAsUnusable() {
        // The stem is judged after canonicalizing, not before: a combining mark is not a letter, so
        // judging first made the same file `main` on a machine that delivers decomposed names.
        assertTrue(!"main".equals(Runner.moduleName(Path.of(NFD + ".sou"))),
                "a decomposed file name is the module its composed spelling would be");
    }

    @Test
    void theGeneratedClassesAreNamedByTheCanonicalModule() {
        Map<String, byte[]> classes = Compiler.compile(HEADERLESS, NFD);
        assertTrue(classes.containsKey(NFC + ".Greet"),
                "generated: " + classes.keySet());
    }

    @Test
    void nothingDecomposedSurvivesIntoTheTree() {
        // The property behind all of the above, asked of the whole tree rather than of one door: a
        // data name, a field name, a type variable and a string literal all written decomposed, and
        // nothing decomposed left once it is parsed. A type variable is only checkable this way —
        // it is a core privilege, so it never reaches a compiled user module.
        Ast.Module parsed = CstFrontend.parse("""
                module souther.probe

                data %s = { %s: String }

                let same (x: '%s) : '%s = x
                let label = "%s"
                """.formatted(NFD, NFD, NFD, NFD, NFD), null);
        assertTrue(!parsed.toString().contains(NFD),
                "something kept the decomposed spelling: " + parsed);
    }

    @Test
    void anIdentifierWrittenTwoWaysIsOneName() {
        // The reference is decomposed and the declaration composed; they meet as one name.
        Compiler.compile("""
                module demo

                data %s = { n: Int }
                data Out = Int

                behavior calc : (v: %s) -> Out constructs Out

                let calc (v) = Out(v.n)
                """.formatted(NFC, NFD));
    }

    @Test
    void aSumCaseNamedTwoWaysIsOneCaseAndRefused() {
        // Targets the case list rather than the declarations: one `data`, named twice in the sum.
        // Before names were canonical these were two cases with one wire tag, so the second was
        // unreachable from outside; now they are one case listed twice, which is already refused.
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data %s
                data Other
                data Flag = %s | %s | Other
                """.formatted(NFC, NFC, NFD)));
        assertTrue(e.getMessage().contains(NFC) || e.getMessage().contains("twice"), e.getMessage());
    }
}
