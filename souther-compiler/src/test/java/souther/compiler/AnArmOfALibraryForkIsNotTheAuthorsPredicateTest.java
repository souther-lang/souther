package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the arms of a library combinator say about the predicates an author handed it, which is
 * nothing — and what they are counted as saying today, which is everything.
 *
 * <p>A row through one {@code List.filter} establishes nothing about the {@code List.filter} beside
 * it. The two are one fork of one declaration inlined twice, and what each decides is the closure it
 * was handed: they part different values and are separately owed. The obligation an arm is counted
 * under is keyed by the construct that wrote the fork, and the fork was written in
 * {@code souther.list} — so both calls come out under one key, and a row that reached either marks
 * both.
 *
 * <p>The model below runs the first predicate and never runs the second: {@code b} is empty, so the
 * fork under it is not entered once. It is reported as every arm covered.
 *
 * <p><b>What this test states is the defect and not the rule.</b> It is written so that the numbers
 * cannot move in silence, and the day the obligation an arm is counted under tells the two calls
 * apart, this fails and is rewritten to say the rule instead. Read as an expectation, it says a
 * behavior may be reported complete over a predicate nothing ran, which is what it exists to keep
 * visible until that is untrue.
 */
class AnArmOfALibraryForkIsNotTheAuthorsPredicateTest {

    private static final String MODULE = "example.people";

    private static final String MODEL = """
            module example.people

            data Age = Int
                invariant value >= 0
            data Person =
                { age: Age
                }

            behavior twice : (a: List<Person>, b: List<Person>) -> List<Person>
            let twice (a, b) =
                List.filter(x -> x.age.value >= 18, a)
                    ++ List.filter(y -> y.age.value >= 65, b)

            example twice
                | "the second predicate is never reached"
                    : ([ Person { age = Age(20) }, Person { age = Age(10) } ], [ ])
                        -> [ Person { age = Age(20) } ]
            """;

    private static Adequacy.BranchEvidence armsOfTwice() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        Map<String, Adequacy.BranchEvidence> arms =
                compilation.db().ask(new Adequacy.BranchCoverage(MODULE)).value();
        assertNotNull(arms, "the model under test compiles");
        Adequacy.BranchEvidence twice = arms.get("twice");
        assertNotNull(twice, "twice has arms to measure");
        return twice;
    }

    /**
     * Four occurrences and two keys: the two calls share both of the fork's arms.
     *
     * <p>This is the whole of it. Everything below follows from the quotient being taken over a key
     * that does not hold which closure the fork was deciding.
     */
    @Test
    void twoCallsOfOneCombinatorShareTheirArms() {
        Adequacy.BranchEvidence twice = armsOfTwice();
        assertEquals(4, twice.all().size(), "each call is emitted and probed on its own");
        assertEquals(2, twice.obligations(),
                "and the two calls are counted under one pair of keys, which is the defect");
    }

    /** So the predicate that never ran is reported covered, and nothing is named unreached. */
    @Test
    void aPredicateNothingRanIsReportedCovered() {
        Adequacy.BranchEvidence twice = armsOfTwice();
        assertEquals(twice.obligations(), twice.coveredObligations(),
                "every key is marked by the row that reached the first call only");
        assertTrue(twice.unreached().isEmpty(),
                () -> "and nothing is named unreached, though `y -> y.age.value >= 65` was not"
                        + " entered once: " + twice.unreached());
    }
}
