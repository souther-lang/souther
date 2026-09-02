package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.check.Prepared;
import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.RuleWithoutALine;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.Shapes;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A rule a body wrote that no reading got through leaves the position short, and every reader says
 * so.
 *
 * <p>The one shape an accounting of questions cannot answer for. A question is raised by a rule of
 * a declaration and is answered by whichever reading took the rule in; a comparison a body writes
 * raises what it asks and answers it in the same breath, so a reading that stopped on one leaves no
 * question standing anywhere. What says the position is short of anything is the finding the reader
 * that stopped made, and nothing else.
 *
 * <p>So a verdict read off the accounting alone had nothing to go on here, and a phase that carried
 * only "a rule is filed at this position" gave the same answer for this and for a rule read from
 * end to end — which is the model stating something. The two are held apart, and this holds every
 * reader of them to the same answer at once: what the position comes to, what stands at it, what
 * the measure's closure says, and what a document names.
 */
class ARuleABodyWroteThatNoReadingGotThroughLeavesThePositionShortTest {

    /**
     * A guard comparing two numbers taken of two positions, which this reading does not take apart.
     *
     * <p>What stopped it is the comparison as a whole: the length of a string against a number an
     * operation answers is a form no reader here turns into a line or into a set of values. The
     * position carries no rule of its own, so nothing else answers for it.
     */
    private static final String A_GUARD_NO_READING_TAKES_APART = """
            module probe

            data Low
            data Ok = { at: Int }

            behavior f : (n: Int, m: Int, s: String) -> Ok | Low
                constructs Ok

            let f (n, m, s) = {
                guard String.length(s) > Int.abs(m) else Low
                Ok { at = n }
            }
            """;

    /** The position the rule is filed at, which is where a reader is sent to look. */
    private static final String AT = "s";

    /** It is not a position the model divides no way, and not one it states something about. */
    @Test
    void thePositionIsOneNothingWasEstablishedAbout() {
        UndividedPosition said = undividedAt(AT);

        assertInstanceOf(UndividedPosition.Why.CannotDerive.class, said.why(), said.toString());
    }

    /** And no question of a rule stands at it, which is what makes this its own shape. */
    @Test
    void noQuestionStandsAtIt() {
        assertEquals(List.of(), divided().unanswered().stream()
                        .filter(each -> each.asks().path().toString().equals(AT)).toList(),
                "a comparison a body writes raises and answers in one breath");
    }

    /** And the reading got to the position, so what is short of it is not the walk. */
    @Test
    void theReadingGotToThePosition() {
        PositionAccount at = divided().positions().stream()
                .filter(each -> each.path().toString().equals(AT)).findFirst().orElseThrow();

        assertEquals(null, at.notReachedInto(), "the walk read into the position");
    }

    /** What says it is short is the finding the reader that stopped made, naming the rule. */
    @Test
    void theRuleThatStoppedIsPublishedWithTheRule() {
        List<RuleWithoutALine> here = divided().rulesWithoutALine().stream()
                .filter(each -> each.at().path().toString().equals(AT)).toList();

        assertFalse(here.isEmpty(), "nothing was published about the position at all");
        assertTrue(here.stream().anyMatch(each ->
                        each.why() instanceof BlockReason.RuleReadingStopped),
                () -> "no reading is said to have stopped here: " + here);
    }

    /**
     * And the measure's closure says the same thing, which is what the two used to disagree about.
     *
     * <p>A rule a reading did not get through leaves the partition measure short of what it would
     * have divided the position by, and the closure has said so all along. A verdict that called
     * the same position one the model states something about was the other half of one rule
     * answered two ways.
     */
    @Test
    void theClosureOfTheMeasureSaysTheSameThing() {
        assertInstanceOf(MeasureClosure.OfThePartition.Open.class, divided().partitionClosure(),
                "the rule leaves the partition measure short");
    }

    private static UndividedPosition undividedAt(String path) {
        return divided().undivided().stream()
                .filter(each -> each.at().toString().equals(path)).findFirst()
                .orElseThrow(() -> new AssertionError(
                        "no position came back undivided at " + path + ": " + divided().undivided()));
    }

    private static Partitions.Partitioning divided() {
        Compilation compilation = Compilation.ofSource(A_GUARD_NO_READING_TAKES_APART, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.diagnostics().values().stream()
                        .flatMap(List::stream).map(Object::toString).toList(),
                "the model this is about is one this compiler accepts");
        String module = compilation.modules().get(0);
        Prepared prepared = compilation.db().ask(new Shapes.Prepared(module)).value();
        Hir.SpecBehavior spec = (Hir.SpecBehavior) prepared.behaviors().stream()
                .filter(each -> each.name().equals("f")).findFirst().orElseThrow();
        return compilation.db().ask(new Adequacy.Divided(module, spec.name())).value();
    }
}
