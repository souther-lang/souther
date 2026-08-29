package souther.compiler.check;

import souther.compiler.Compiler;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.Note;
import souther.compiler.diag.msg.InvariantMessage;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What E2011 tells an author to do, and what doing it costs.
 *
 * <p>The warning used to name a guard as the mechanism and then offer a move that is not always
 * there: "reify the relation into an input's invariant" reads as a clause added to an input the
 * behavior already takes, and a relation between two parameters belongs to no input, so for the
 * case that most needs the advice there is nothing to add it to (#965). What is there instead is to
 * introduce the data that holds both values.
 *
 * <p>So the hint states the modelling question rather than a list of moves. It has two answers —
 * whether the inputs the construction fails for are inputs the behavior takes — and three
 * spellings, because the first answer may be written as a guard or as an attempt. There is no
 * fourth spelling that leaves the construction as written and accepts the abort, and this fixes
 * that there is not: the run-time check is the safety net for a model bug, not a way to record an
 * unanswered question in the source.
 *
 * <p>Every silent case here has a neighbour differing in one thing that is not silent, and the
 * warned case is the same construction as all of them.
 */
class AnUnprovenConstructionHasTwoAnswersAndThreeSpellingsTest {

    private static final String TYPES = """
            module demo

            data U = Int
                invariant nonNeg = value >= 0

            data Negative

            data Reduction =
                { shotei: Int
                , gen: Int
                }
                invariant enough = shotei >= gen
            """;

    /** Two parameters and a difference over them: the relation belongs to no input there is. */
    private static final String UNANSWERED = """
            behavior f : (shotei: Int, gen: Int) -> U
                constructs U
            let f (shotei, gen) = U(shotei - gen)
            """;

    /** The first answer, written as a guard: the failing inputs are ones `f` takes. */
    private static final String GUARDED = """
            behavior f : (shotei: Int, gen: Int) -> U | Negative
                constructs U
            let f (shotei, gen) = {
                guard shotei - gen >= 0 else Negative
                U(shotei - gen)
            }
            """;

    /** The same answer, written once: the invariant itself decides the branch. */
    private static final String ATTEMPTED = """
            behavior f : (shotei: Int, gen: Int) -> U | Negative
                constructs U
            let f (shotei, gen) = {
                guard U(shotei - gen) as u else Negative
                u
            }
            """;

    /** The second answer: a data owns the relation and is what the behavior takes. */
    private static final String OWNED = """
            behavior f : (r: Reduction) -> U
                constructs U
            let f (r) = U(r.shotei - r.gen)
            """;

    private static List<Diagnostic> warnings(String body) {
        return Compiler.compileModulesWithWarnings(List.of(TYPES + "\n" + body)).warnings().stream()
                .filter(d -> "E2011".equals(d.code())).toList();
    }

    private static Diagnostic warning(String body) {
        List<Diagnostic> found = warnings(body);
        assertEquals(1, found.size(), found.toString());
        return found.get(0);
    }

    // --- what the author is told ---------------------------------------------------------------

    /**
     * The hint names the question and not a guard.
     *
     * <p>Held by identity rather than by the words it renders as: what may not come back is the
     * advice to add a clause to an input, which is the move #965 found there was nowhere to make.
     */
    @Test
    void theHintStatesTheModellingQuestion() {
        Diagnostic said = warning(UNANSWERED);

        assertInstanceOf(InvariantMessage.NothingKnownHereEstablishes.class, said.said(),
                "the clause is named, and what is reported is what is known and not what a guard"
                        + " did");
        assertTrue(said.notes().stream().map(Note::said).anyMatch(
                        one -> one instanceof InvariantMessage.GuardItOrLetADataOwnTheRelation),
                "and the author is asked whether these are inputs the behavior takes");
    }

    // --- the three spellings -------------------------------------------------------------------

    /** The failing inputs are ones the behavior takes, and the failure is written as a branch. */
    @Test
    void aGuardAnswersIt() {
        assertEquals(List.of(), warnings(GUARDED));
    }

    /**
     * The same answer with the rule written once. An attempt is not a fourth spelling that accepts
     * the abort: its `else` names a business failure, so what it does is turn a construction that
     * could abort into a branch (ADR-0070).
     */
    @Test
    void anAttemptAnswersItToo() {
        assertEquals(List.of(), warnings(ATTEMPTED));
    }

    /**
     * The failing inputs are not ones the model admits, and a data says so.
     *
     * <p>Nothing here is guarded. What discharges the construction is what `Reduction` declares,
     * seeded where the behavior's input is read — which is why the warning is worded about what is
     * known and not about what a guard established.
     */
    @Test
    void aDataThatOwnsTheRelationAnswersItWithNoGuardAtAll() {
        assertEquals(List.of(), warnings(OWNED));
    }

    // --- and the neighbour that is not silent --------------------------------------------------

    /**
     * The same difference over the same two values, taken as two parameters rather than as one
     * data. This is the row #965 is about: nothing about the arithmetic changed, only where the
     * relation is written, and there is no way to write it on the behavior.
     */
    @Test
    void takingTheSameTwoValuesSeparatelyIsNotAnswered() {
        assertEquals(1, warnings(UNANSWERED).size(),
                "the relation `Reduction` owns is not stated anywhere the two parameters reach");
    }
}
