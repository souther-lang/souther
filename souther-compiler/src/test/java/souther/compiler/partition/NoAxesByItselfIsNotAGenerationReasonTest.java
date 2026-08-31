package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.check.Symbols;
import souther.compiler.query.ReadAs;
import souther.compiler.reading.CoverageRead;
import souther.compiler.reading.PathAccess;
import souther.compiler.types.Type;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A behavior the model divides nowhere still gets the answers its arms have.
 *
 * <p>The search over the classes has nothing to walk where no position is divided, and it used to
 * return there — taking the arms with it, which do not read the classes for their answer. What it
 * takes to arrive at an arm is what the reading of the body says, and that reading is made before
 * the search is called. An arm it has an answer for was left with no entry at all, and whoever read
 * the result for one had nothing to go on but the absence.
 *
 * <p>And no reason is written for it either. Nothing being divided is a fact about the classes and
 * not something that happened to this generation: a reason here would be a sentence about the whole
 * run, read beside rows it is not short of. What does belong in the reasons — the rows could not be
 * read, the classes would not link — is written by whatever established it, and having no axis is
 * not one of those.
 */
class NoAxesByItselfIsNotAGenerationReasonTest {

    private static final Symbols SYMBOLS = Symbols.none(DefaultStdlib.get());

    private static final PathAccess NOT_ENUMERABLE =
            new PathAccess.Unsupported(PathAccess.Unsupported.Why.WAYS_NOT_ENUMERABLE);

    /** The reading of an input of one parameter, which is what says what a number of it is measured
     *  on. */
    private static souther.compiler.inputs.Quantities readingOf(String parameter, Type type) {
        return souther.compiler.inputs.InputDomain.of(
                List.of(new souther.compiler.inputs.InputDomain.Parameter(parameter, null, type)),
                SYMBOLS, ReadAs.THE_COMPILATION_DOES).quantities(SYMBOLS);
    }

    @Test
    void anArmIsAnsweredWhereNoPositionIsDivided() {
        FillResult filled = filledOverOneArm();

        assertEquals(Map.of(new Generator.ArmOwed(1), new ArmDisposition.NoWayIn(NOT_ENUMERABLE)),
                filled.discharge().arms(),
                "the arm's own entry, in the words the reading of the body used");
    }

    @Test
    void havingNoAxisIsNotWrittenDownAsAReason() {
        FillResult filled = filledOverOneArm();

        assertEquals(List.of(), filled.reasons(),
                "nothing happened to this generation that a reader is owed a sentence about");
    }

    /** One arm the reading has an answer for, over a behavior whose position nothing divides. */
    private static FillResult filledOverOneArm() {
        Generator.Subject subject = new Generator.Subject("fee",
                new BehaviorInputs(List.of("days"), List.of(Type.INT), SYMBOLS,
                        ReadAs.THE_COMPILATION_DOES),
                readingOf("days", Type.INT), List.of(), HeldCounts.NONE);
        java.util.SequencedMap<Integer, PathAccess> ways = new java.util.LinkedHashMap<>();
        ways.put(1, NOT_ENUMERABLE);
        CoverageRead.Read read = new CoverageRead.Read(List.of(), ways);

        return Generator.fill(subject, List.of(), Generator.CandidateCheck.ANY, read,
                Generator.Trial.NOTHING_RUNS, List.of(), List.of(), List.of(1),
                Budgets.generation());
    }
}
