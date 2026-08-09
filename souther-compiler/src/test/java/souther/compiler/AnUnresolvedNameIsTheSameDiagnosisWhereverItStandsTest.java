package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.CompileException;

import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a name that resolves to nothing is reported as, wherever it was written.
 *
 * <p>One fact is established — the lookup came back with nothing — and one thing follows from it:
 * this name is not in scope. Where the name stood when it failed to resolve is a fact about the
 * source and not about the name, so it decides what else may be offered and not what the failure is.
 *
 * <p>Held against every embedding rather than against the one that was reported, because the defect
 * was a second answer for the same fact: a name applied to arguments was reported as a call to
 * something on the JVM, which is a cause nothing here establishes and which sent an author who had
 * left a name off an import list to go and write a Java class.
 */
class AnUnresolvedNameIsTheSameDiagnosisWhereverItStandsTest {

    private static final String TYPES = """
            module t exposing (Out, f)

            data Out = { v: Int }

            let twice (n: Int) : Int = n + n
            """;

    private static final String BEHAVIOR = """
            behavior f : (n: Int) -> Out
                constructs Out
            """;

    private static String verdict(String body) {
        try {
            Compiler.compile(TYPES + "\n" + BEHAVIOR + "\nlet f (n) = " + body + "\n");
            return "ok";
        } catch (CompileException e) {
            return e.diagnostic().code();
        }
    }

    /**
     * Every embedding of an unresolved name is the same diagnosis.
     *
     * <p>Asked as one map, because what is held is that the answer does not vary — a single case
     * fixing one embedding is satisfied by a second answer written for the others.
     */
    @Test
    void everyEmbeddingOfAnUnresolvedNameIsANamingError() {
        Map<String, String> embeddings = new LinkedHashMap<>();
        embeddings.put("as a value", "Out { v = Missing }");
        embeddings.put("applied", "Out { v = Missing(n) }");
        embeddings.put("handed to a helper", "Out { v = twice(Missing) }");
        embeddings.put("applied inside an application", "Out { v = twice(Missing(n)) }");
        embeddings.put("applied to nothing", "Out { v = Missing() }");

        Map<String, String> expected = new LinkedHashMap<>(embeddings);
        expected.replaceAll((_, _) -> "E1023");
        assertEquals(expected, verdicts(embeddings));
    }

    /**
     * A member a module of this compilation has not got is the same again.
     *
     * <p>The qualifier resolves and the member does not, which is one lookup coming back with
     * nothing however the name was spelled. Applying it says no more about the JVM than writing it
     * bare does.
     */
    @Test
    void aMemberARealModuleHasNotGotIsANamingErrorAppliedOrNot() {
        String up = """
                module up exposing (Amount)

                data Amount = Int
                """;
        String down = """
                module down exposing (Out, f)

                import up (Amount)

                data Out = { v: Int }

                behavior f : (n: Int) -> Out
                    constructs Out

                let f (n) = Out { v = %s }
                """;

        assertEquals("E1023", codeOf(up, down.formatted("up.noSuch")), "written bare");
        assertEquals("E1023", codeOf(up, down.formatted("up.noSuch(n)")), "and applied");
    }

    /**
     * What the failure is and what to do about it are two things, and only the first is fixed here.
     *
     * <p>A near spelling is worth offering and is offered; it is carried beside the diagnosis rather
     * than deciding it. The defect this replaces had the remediation choosing the cause — the advice
     * to implement the name from Java was what made the report say the name was a JVM call.
     */
    @Test
    void aNearSpellingIsOfferedBesideTheDiagnosisAndDoesNotDecideIt() {
        String source = TYPES + "\n" + BEHAVIOR + "\nlet f (n) = Out { v = twise(n) }\n";
        CompileException e = org.junit.jupiter.api.Assertions.assertThrows(
                CompileException.class, () -> Compiler.compile(source));

        assertEquals("E1023", e.diagnostic().code());
        assertTrue(e.getMessage().contains("twice"),
                "the near spelling is offered: " + e.getMessage());
    }

    /**
     * A name another module of this compilation exposes is still not in scope, and the report says
     * where it is.
     *
     * <p>The commonest way to reach an unresolved name is to leave one off an import list, and the
     * spelling suggestion cannot help there: it offers names within reach, and this one is not. What
     * the compiler knows is that a module of this compilation has it, which is a fact and not an
     * instruction — reaching it qualified needs no import at all.
     */
    @Test
    void aNameAnotherModuleExposesIsSaidToBeThere() {
        String up = """
                module up exposing (Amount)

                data Amount = Int
                """;
        String down = """
                module down exposing (Out, f)

                data Out = { v: Int }

                behavior f : (n: Int) -> Out
                    constructs Out

                let f (n) = Out { v = Amount(n).value }
                """;
        String reported = messageOf(up, down);

        assertTrue(reported.contains("E1023"), reported);
        assertTrue(reported.contains("`up` exposes `Amount`"), reported);
    }

    /**
     * Two modules exposing the spelling is no answer, so none is given.
     *
     * <p>A hint naming one of them is a guess, and the reader is already being told the name is not
     * in scope. The diagnosis does not change.
     */
    @Test
    void aSpellingTwoModulesExposeIsLeftWithoutAModuleToName() {
        String up = """
                module up exposing (Amount)

                data Amount = Int
                """;
        String other = """
                module other exposing (Amount)

                data Amount = Int
                """;
        String down = """
                module down exposing (Out, f)

                data Out = { v: Int }

                behavior f : (n: Int) -> Out
                    constructs Out

                let f (n) = Out { v = Amount(n).value }
                """;
        String reported = messageOf(up, other, down);

        assertTrue(reported.contains("E1023"), reported);
        assertFalse(reported.contains("exposes `Amount`"), reported);
    }

    private static Map<String, String> verdicts(Map<String, String> bodies) {
        Map<String, String> out = new LinkedHashMap<>();
        bodies.forEach((where, body) -> out.put(where, verdict(body)));
        return out;
    }

    /** What a multi-module compilation was refused with, rendered the way an author reads it. */
    private static String messageOf(String... sources) {
        CompileException e = org.junit.jupiter.api.Assertions.assertThrows(CompileException.class,
                () -> Compiler.compileModules(java.util.List.of(sources)));
        return e.diagnostic().code() + " " + e.getMessage();
    }

    /** The code a multi-module compilation is refused with. */
    private static String codeOf(String... sources) {
        try {
            Compiler.compileModules(java.util.List.of(sources));
            return "ok";
        } catch (CompileException e) {
            return e.diagnostic().code();
        }
    }
}
