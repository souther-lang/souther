package souther.compiler.partition;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import java.util.List;
import java.util.Map;
import java.util.TreeSet;
import java.util.concurrent.ConcurrentHashMap;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A clause is evaluated as it is written: the conjuncts of a rule run left to right and the run
 * aborts at the first that does not hold. So a statement the ones before it keep a run from is
 * owed no question about being read, and the same statement where the compiler cannot show that
 * keeps its question.
 *
 * <p>Only what a statement owes for being read depends on that order. The lines a clause draws are
 * the relation's and are the same wherever its conjuncts stand, which is asked of the lines too.
 */
class AnEnsuresStatementNoRunEvaluatesOwesNothingTest {

    private static final Map<String, Compilation> MEASURED = new ConcurrentHashMap<>();

    private static final String MODEL = """
            module demo
            data Yes = { n: Int }
            data No = { n: Int }
            data Terms = Net15 | Net30 | Eom
            let weekday (c: Date, d: Date): Int = Int.floorMod(Date.daysBetween(c, d), 7)
            let inner (t: Terms, c: Date, d: Date): Bool =
                t == Net15 && weekday(c, Date.addMonths(1, d)) >= 1
            behavior g : (c: Date, d: Date, t: Terms, n: Int, xs: List<Int>) -> Yes | No
                ensures Yes -> %s
            let g (c, d, t, n, xs) = if t == Eom then Yes { n = 1 } else No { n = 0 }
            """;

    /** A stop of the reading, whatever it is compared with. */
    private static final String STOP = "weekday(c, Date.addMonths(1, d)) >= 1";

    /** A form nothing reads, so the statement is one the clause reader turns away. */
    private static final String OPAQUE = "List.contains(0, xs)";

    @Test
    void aStatementTheOnesBeforeItKeepARunFromOwesNothing() {
        assertNothingOwed("t == Eom && t == Net15 && " + STOP);
        assertNothingOwed("t == Eom && t == Net15 && " + OPAQUE);
    }

    /** The same after a helper is expanded into the clause: its own conjunction is walked too. */
    @Test
    void aStatementBehindAHelpersConjunctionIsAskedTheSameWay() {
        assertNothingOwed("t == Eom && inner(t, c, d)");
        assertEquals(entriesOf(STOP), entriesOf("t == Net15 && inner(t, c, d)"));
    }

    @Test
    void theSameStatementsWhereTheWayIsNotShownEmptyOweWhatTheyOweAlone() {
        for (String statement : List.of(STOP, OPAQUE)) {
            List<String> alone = entriesOf(statement);
            assertFalse(alone.isEmpty(), "the control owes something: " + statement);
            assertEquals(alone, entriesOf("t == Eom && " + statement), statement);
            assertEquals(alone, entriesOf("t == Net15 && " + statement), statement);
        }
    }

    /**
     * What an earlier statement the compiler cannot say as a condition proves nothing, so the
     * statement after it is owed as it was; and one it can say still turns a later one away, with
     * the cannot-say statement between them owed only what it owes alone.
     */
    @Test
    void aStatementTheCompilerCannotSayProvesNothingAndIsStillOwedItsOwn() {
        assertEquals(entriesOf(OPAQUE + " && " + STOP),
                entriesOf("t == Eom && " + OPAQUE + " && " + STOP));
        assertEquals(entriesOf(OPAQUE), entriesOf("t == Eom && " + OPAQUE
                + " && t == Net15 && " + STOP));
    }

    /** The lines are the relation's: a statement no run evaluates draws the line it draws. */
    @Test
    void theLinesAClauseDrawsDoNotTurnOnTheOrderItIsWrittenIn() {
        List<String> alone = linesOf("n > 3");
        assertFalse(alone.isEmpty());
        assertEquals(alone, linesOf("t == Eom && t == Net15 && n > 3"));
        assertEquals(alone, linesOf("n > 3 && t == Eom && t == Net15"));
    }

    private static void assertNothingOwed(String clause) {
        PartitionEvidence evidence = evidenceOf(clause);
        assertEquals(List.of(), entriesOf(evidence), clause);
        assertEquals(List.of(), evidence.unanswered(), clause);
    }

    private static List<String> entriesOf(String clause) {
        return entriesOf(evidenceOf(clause));
    }

    private static List<String> entriesOf(PartitionEvidence evidence) {
        return evidence.notRead().stream()
                .map(each -> each.at() + " " + each.reason() + " " + each.readingStopped())
                .sorted().toList();
    }

    private static List<String> linesOf(String clause) {
        List<BorderAssessment> lines = Adequacy.readingsOf(compile(clause).db(), "demo").get("g");
        TreeSet<String> out = new TreeSet<>();
        if (lines != null) {
            lines.forEach(each -> out.add(each.left() + " " + each.value()));
        }
        return List.copyOf(out);
    }

    private static PartitionEvidence evidenceOf(String clause) {
        return compile(clause).db().ask(new Adequacy.Coverage("demo")).value().get("g");
    }

    /** Each clause is measured once, however many of the questions above ask about it. */
    private static Compilation compile(String clause) {
        return MEASURED.computeIfAbsent(clause, written -> {
            Compilation compilation = Compilation.ofSource(MODEL.formatted(written), "Main");
            compilation.measure(Adequacy.Asked.fullReport());
            compilation.answerEverything();
            assertEquals(List.of(), compilation.errors(), written);
            return compilation;
        });
    }

    /** And given back when the class is done with them: a fork keeps its JVM. */
    @AfterAll
    static void released() {
        MEASURED.clear();
    }
}
