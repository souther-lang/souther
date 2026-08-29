package souther.cli;

import souther.compiler.Reserved;
import souther.compiler.Compiler;
import souther.compiler.diag.CompileException;
import souther.compiler.frontend.CstFrontend;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Ast;
import souther.compiler.jvm.ClassFileImage;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
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
 * <p>Every door is walked here: an identifier, a type variable, the module name a header-less source
 * is given, the file stem the CLI derives one from, and the identifiers an invocation names on the
 * command line ({@code run --behavior}, {@code examples --module}, {@code examples --behavior}).
 * The last three are one line each in the argument parser, and a line is exactly what gets deleted
 * by someone who cannot see what it is for — so each is driven rather than described.
 *
 * <p>What is canonical is what a name is called. What the author typed is kept beside it and is not
 * canonical, which is the whole of {@code WrittenName} and is asserted here too — otherwise a tree
 * that had thrown the spelling away would pass this class as readily as one that had not.
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
        Map<String, ClassFileImage> classes = Compiler.compile(HEADERLESS, NFD);
        assertTrue(classes.containsKey(NFC + ".Greet"),
                "generated: " + classes.keySet());
    }

    /** A data name, a field name, a type variable and a string literal, all written decomposed. A
     *  type variable is only checkable this way — it is a core privilege, so it never reaches a
     *  compiled user module. */
    private static Ast.Module decomposedThroughout() {
        return CstFrontend.parse("""
                module souther.probe

                data %s = { %s: String }

                let same (x: '%s) : '%s = x
                let label = "%s"
                """.formatted(NFD, NFD, NFD, NFD, NFD), null);
    }

    @Test
    void everyNameInTheTreeIsCanonicalWhicheverWayItWasWritten() {
        // The property behind all of the above, asked of the whole tree rather than of one door.
        // `toString` reaches every name, and a name reads as what it is called.
        assertTrue(!decomposedThroughout().toString().contains(NFD),
                "something is called by its decomposed spelling: " + decomposedThroughout());
    }

    @Test
    void aNameKeepsTheDecomposedSpellingItWasWrittenWith() {
        // The other half, and the reason the assertion above is not the whole story: what a name is
        // called is canonical and what the file says is not, so the decomposed characters are still
        // in the tree — in the occurrence, which is what a report quotes and an editor measures.
        Ast.Def data = decomposedThroughout().defs().get(0);

        assertEquals(NFC, data.name());
        assertEquals(NFD, data.written().spelling(),
                "the declaration no longer says what the author typed");
    }

    @Test
    void aStringLiteralIsCanonicalizedAsAValueAndKeepsNoSpelling() {
        // A literal is not a name. It crosses a boundary as a value, so what it holds is the
        // canonical text itself and there is no second answer to keep (ADR-0096).
        Ast.FnDef label = decomposedThroughout().fns().stream()
                .filter(fn -> fn.name().equals("label")).findFirst().orElseThrow();

        assertEquals(NFC, assertInstanceOf(Ast.StringLit.class, label.writtenBody()).value());
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

    /** The two spellings written the same way, for a fixture that has to be read as characters. */
    private static final String CANONICAL_BEHAVIOR = """
            module demo

            behavior %s : (n: Int) -> Int

            let %s (n) = n
            """.formatted(NFC, NFC);

    @Test
    void aBehaviorAnInvocationNamesDecomposedIsTheOneTheModuleDeclares() throws Exception {
        Path file = Files.createTempDirectory("souther-doors").resolve("demo.sou");
        Files.writeString(file, CANONICAL_BEHAVIOR);

        assertEquals("7", Runner.run(file, NFD, "7"),
                "`run --behavior` is a name arriving from outside");
    }

    @Test
    void aModuleAnInvocationNamesDecomposedIsTheOneTheSourceDeclares() throws Exception {
        String reported = examplesOf("module " + NFC + """
                \n
                behavior only : (n: Int) -> Int

                let only (n) = n
                """, "--module", NFD);

        assertTrue(reported.contains("only"),
                "the report was filtered to a module the argument does not spell: " + reported);
    }

    @Test
    void aBehaviorTheExamplesReportIsFilteredToMayBeNamedDecomposed() throws Exception {
        String reported = examplesOf(CANONICAL_BEHAVIOR, "--behavior", NFD);

        assertTrue(reported.contains(NFC),
                "the report was filtered to a behavior the argument does not spell: " + reported);
    }

    /** What {@code souther examples} writes for {@code source}, run with {@code args}. */
    private static String examplesOf(String source, String... args) throws Exception {
        Path file = Files.createTempDirectory("souther-doors").resolve("demo.sou");
        Files.writeString(file, source);
        List<String> argv = new ArrayList<>(List.of("examples", file.toString()));
        argv.addAll(List.of(args));
        PrintStream originalOut = System.out;
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        System.setOut(new PrintStream(out, true, StandardCharsets.UTF_8));
        try {
            Main.main(argv.toArray(String[]::new));
        } finally {
            System.setOut(originalOut);
        }
        return out.toString(StandardCharsets.UTF_8);
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
