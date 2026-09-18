package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.WhereItSits;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.Primary;
import souther.compiler.diag.msg.DataMessage;
import souther.compiler.diag.msg.DeclarationMessage;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Answer;
import souther.compiler.query.Compilation;
import souther.compiler.query.Shapes;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertAll;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A data is not made of itself, and that is settled before anything reads what one holds.
 *
 * <p>A value of a product holds the fields of everything it spreads, so a declaration that spreads
 * its way round to itself describes no value — and every walk over the spreads runs until the stack
 * does. The rule is answered from the declarations alone ({@link ProductSpreads}) and what reads a
 * declaration is asked afterwards, which is what these hold to: the refusal arrives as a sentence
 * about the declaration, and the readers that walk the spreads are never started.
 *
 * <p><b>A data reached twice is not this.</b> Two spreads meeting one declaration bring its fields
 * in twice, which is a field written twice and stays that refusal — the case below that says so is
 * what keeps this check about rings rather than about a declaration being reached more than once.
 */
class ADataThatSpreadsItsWayBackToItselfIsRefusedTest {

    /** A data spreading itself, which is the ring said in one line. */
    private static final String ITSELF = """
            module demo exposing ( Pair )

            data Pair = { ...Pair, qty: Int }
            """;

    /** Two that spread each other. */
    private static final String TWO = """
            module demo exposing ( Pair, Other )

            data Pair  = { ...Other, qty: Int }

            data Other = { ...Pair, note: String }
            """;

    /** And a ring of three, which is what says the walk goes round rather than one step back. */
    private static final String THREE = """
            module demo exposing ( A, B, C )

            data A = { ...C, a: Int }

            data B = { ...A, b: Int }

            data C = { ...B, c: Int }
            """;

    /**
     * Two spreads that reach one declaration, which is a field collision and not a ring. Without
     * this, a walk cutting wherever it met a declaration it had already been to would pass every
     * case above and take that refusal away.
     */
    private static final String THE_PATHS_MEET = """
            module demo exposing ( Held, Left, Right, Both )

            data Held = { n: Int }

            data Left = { ...Held, l: Bool }

            data Right = { ...Held, r: Bool }

            data Both = { ...Left, ...Right }
            """;

    @Test
    void aDataThatSpreadsItselfIsToldSoAndNamesTheSpreadsItGoesRoundBy() {
        assertAll(
                () -> assertEquals(new DataMessage.ADataSpreadsItself("Pair", "`Pair`"),
                        whatItSays(ITSELF).first().said(),
                        "one spread, and the declaration it goes round by is its own"),
                () -> assertEquals(new DataMessage.ADataSpreadsItself("Pair", "`Other` -> `Pair`"),
                        whatItSays(TWO).first().said(),
                        "both spreads, in the order they are gone round by"),
                () -> assertEquals(new DataMessage.ADataSpreadsItself("A", "`C` -> `B` -> `A`"),
                        whatItSays(THREE).first().said(),
                        "a ring of three is gone round by three spreads"));
    }

    /** At the spread the ring is entered by — a `...` the author can take out, and not the header
     *  of the declaration it is written on. */
    @Test
    void itIsSaidAtTheSpreadTheRingIsEnteredBy() {
        Reported said = whatItSays(TWO);
        assertEquals(3, WhereItSits.in(TWO,
                        ((Primary.InSource) said.first().primary()).place().region())
                        .start().line(),
                "`...Other` is written on line 3, and that is the line to change");
    }

    /**
     * Nothing that walks the spreads is started on the ring.
     *
     * <p>What says so is that the compile ends with this one sentence: the count of what a
     * declaration's values are and the elaboration of its rules both walk the spreads, and either
     * of them reaching the ring is either a second report or no report at all.
     */
    @Test
    void theReadersThatWalkTheSpreadsAreNotStarted() {
        Compilation c = compiled(TWO);
        assertAll(
                () -> assertEquals(1, c.db().allReports().size(),
                        () -> "the ring is said once and nothing under it is read: "
                                + c.db().allReports()),
                () -> assertFalse(c.db().ask(new Shapes.TypesWithNoValue("demo")).present(),
                        "what a count would walk has no end, so there is no count"),
                () -> assertFalse(c.db().ask(new Shapes.ValueShapes("demo")).present(),
                        "and no reading of the rules either"));
    }

    /** The answer a reader takes: which declarations were established free of rings. */
    @Test
    void whatIsHandedOnIsTheGraphTheWalkWentOver() {
        Answer<ProductSpreads.WellFounded> validated =
                compiled(THE_PATHS_MEET).db().ask(new Shapes.WellFoundedSpreads("demo"));

        assertTrue(validated.present(), "two spreads meeting one declaration close no ring");
        assertEquals(declarations("Held", "Left", "Right", "Both"),
                validated.value().validated(),
                "every declaration the walk went over, its own and the ones its spreads reach");
    }

    /** And the collision they are is still the collision, still naming the spreads that supplied
     *  the field. */
    @Test
    void twoSpreadsThatMeetOneDeclarationAreStillAFieldWrittenTwice() {
        Reported said = whatItSays(THE_PATHS_MEET);
        assertEquals(new DataMessage.SpreadFieldCollision("n", "Right", "...Left"),
                said.first().said(),
                () -> "a data reached twice is a field written twice, and the two spreads that"
                        + " supplied it are named: " + said.sentences());
    }

    /**
     * A ring closes inside one module, which is why the refusal is said by the module it is found
     * from and nobody asks whose declaration it is.
     *
     * <p>Held as a check rather than said beside the report. What makes it so is another rule — a
     * spread into another module and back is two modules importing each other — and a language that
     * came to allow that would leave the sentence standing and the same ring reported by each of
     * them.
     */
    @Test
    void aSpreadDoesNotCrossIntoAnotherModuleAndBack() {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("a.sou", """
                module a exposing ( Pair )

                import b

                data Pair = { ...Other, qty: Int }
                """);
        byId.put("b.sou", """
                module b exposing ( Other )

                import a

                data Other = { ...Pair, note: String }
                """);
        Compilation c = Compilation.ofDocuments(byId, Set.of(), ModulePath.EMPTY);
        c.answerEverything();

        assertEquals(List.of(new DeclarationMessage.CyclicModuleDependency()),
                c.db().allReports().stream().map(found -> found.report().diagnostic().said())
                        .toList(),
                "the modules a ring would have to span cannot see each other");
    }

    /** A chain of spreads, which is what says the refusals above are about the ring closing. */
    @Test
    void aChainOfSpreadsIsWrittenAsItReads() {
        Reported said = whatItSays("""
                module demo exposing ( Held, Left, Both )

                data Held = { n: Int }

                data Left = { ...Held, l: Bool }

                data Both = { ...Left, b: Bool }
                """);

        assertEquals(List.of(), said.diagnostics(),
                "nothing in a chain spreads its way back to anything");
    }

    private static Set<TypeSymbol.AtModule> declarations(String... names) {
        Set<TypeSymbol.AtModule> declared = new LinkedHashSet<>();
        for (String name : names) {
            declared.add(TypeSymbols.declared(new TypeKey("demo", name)));
        }
        return declared;
    }

    /** What compiling {@code source} said, as the diagnostics it came to. */
    private record Reported(List<Diagnostic> diagnostics) {

        private Diagnostic first() {
            return diagnostics.get(0);
        }

        private String sentences() {
            return diagnostics.stream().map(Diagnostic::said).toList().toString();
        }
    }

    /** Whether the refusal is reported or raised is not what any of these is about — a compile of
     *  one of these sources says what it says either way. */
    private static Reported whatItSays(String source) {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("m.sou", source);
        Compilation c = Compilation.ofDocuments(byId, Set.of(), ModulePath.EMPTY);
        List<Diagnostic> said = new ArrayList<>();
        try {
            c.answerEverything();
        } catch (CompileException e) {
            said.addAll(e.diagnostics());
        }
        c.db().allReports().forEach(found -> said.add(found.report().diagnostic()));
        return new Reported(said);
    }

    /** The compilation itself, for a case that asks it what it holds rather than what it said. */
    private static Compilation compiled(String source) {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("m.sou", source);
        Compilation c = Compilation.ofDocuments(byId, Set.of(), ModulePath.EMPTY);
        try {
            c.answerEverything();
        } catch (CompileException _) {
            // What it refused is another case's; this one reads an answer it reached on the way.
        }
        return c;
    }
}
