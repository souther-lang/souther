package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.CompileException;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Compilation;
import souther.compiler.query.Db;
import souther.compiler.query.Shapes;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A helper whose parameter its body types, and whose body matches on a sum, is typed while what the
 * module's declarations say is still being worked out.
 *
 * <p>The module's helpers are settled on the way to what its invariants state, and so before what
 * any declaration of the module says. A {@code match} in one of them asks which cases its subject
 * has and what an arm binds, and a sum's cases are settled where its names resolve — so the match is
 * answered from there, and never by asking what the sum says.
 *
 * <p>Each row leaves {@code d} for the body to type, and the body types it only through what an arm
 * binds: written out as {@code d: A}, none of them reaches the question at all.
 */
class AHelperMatchingASumIsTypedWhileTheDeclarationsAreBeingMadeTest {

    private static final String SUM = """
            module m

            data A = { n: Int }
            data B = { k: Int }
            data S = A | B
            """;

    @Test
    void aHelperNoInvariantCallsIsTypedFromTheCaseAnArmBinds() {
        assertDoesNotThrow(() -> Compiler.compile(SUM + """

                let same (s: S, d) = match s with
                    | A as v -> v == d
                    | B -> false

                behavior f : (s: S, a: A) -> Bool
                let f (s, a) = same(s, a)
                """));
    }

    @Test
    void anOrPatternArmBindsWhatItsAlternativesHaveInCommon() {
        assertDoesNotThrow(() -> Compiler.compile(SUM + """

                let same (s: S, d) = match s with
                    | A | B as v -> v == d

                behavior f : (s: S, a: A) -> Bool
                let f (s, a) = same(s, a)
                """));
    }

    @Test
    void aHelperAnInvariantCallsIsTypedFromTheCaseAnArmBinds() {
        assertDoesNotThrow(() -> Compiler.compile(SUM + """

                let same (s: S, d) = match s with
                    | A as v -> v == d
                    | B -> false

                data X = { s: S, a: A }
                    invariant same(s, a)
                """));
    }

    /** The descent under a case that is itself a sum is read from what each sum lists as well. */
    @Test
    void aSumWhoseCaseIsASumIsDescendedFromWhatEachLists() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module m

                data A = { n: Int }
                data B = { k: Int }
                data C = { c: Int }
                data T = A | B
                data S = T | C

                let same (s: S, d) = match s with
                    | A as v -> v == d
                    | B | C -> false

                data X = { s: S, a: A }
                    invariant same(s, a)
                """));
    }

    /**
     * An arm naming no case of the subject is refused as such. What says which other sum it is a
     * case of looks at what every sum in scope lists, and does it while the helper is typed too.
     */
    @Test
    void anArmNamingNoCaseOfTheSubjectIsReportedAsThat() {
        CompileException refused = assertThrows(CompileException.class,
                () -> Compiler.compile(SUM + """

                        data C = { c: Int }

                        let same (s: S, d) = match s with
                            | A as v -> v == d
                            | C -> false

                        data X = { s: S, a: A }
                            invariant same(s, a)
                        """));
        assertEquals("E1203", refused.diagnostic().code(), refused::getMessage);
        assertTrue(refused.getMessage().contains("`C` is not a case of data `S`"),
                refused::getMessage);
    }

    /** A sum the language declares lists its cases as one a module declares does. */
    @Test
    void aSumTheLanguageDeclaresIsMatchedTheSameWay() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module m

                let same (mode: RoundingMode, d) = match mode with
                    | HALF_UP as v -> v == d
                    | HALF_EVEN | HALF_DOWN | UP | DOWN | CEILING | FLOOR -> false

                data In = { n: Int }

                behavior f : (i: In) -> Bool
                let f (i) = same(HALF_EVEN, HALF_UP)
                """));
    }

    /**
     * What a value of a sum the language declares can be, as the compilation answers it: read from
     * what that sum lists, which no module of the compilation wrote.
     */
    @Test
    void theCompilationAnswersWhatASumTheLanguageDeclaresCanBe() {
        Db db = Compilation.ofSources(List.of(SUM), ModulePath.EMPTY).db();
        TypeSymbol.AtModule roundingMode =
                TypeSymbols.declared(new TypeKey("souther.decimal", "RoundingMode"));

        assertEquals(List.of("HALF_UP", "HALF_EVEN", "HALF_DOWN", "UP", "DOWN", "CEILING", "FLOOR"),
                Shapes.sumCases(db).of(roundingMode).cases().stream().map(TypeSymbol::name)
                        .toList());
    }
}
