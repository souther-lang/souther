package souther.architecture;

import org.junit.jupiter.api.Test;

import java.lang.classfile.ClassModel;
import java.lang.classfile.MethodModel;
import java.lang.classfile.instruction.InvokeInstruction;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A block is a set of positions and holds no order over them, and no reader takes one off it.
 *
 * <p>{@link souther.compiler.values.Sameness.Block} says this of itself: its members are held in
 * whatever order they arrived in, that order is a fact about how one block was built rather than
 * about which block it is, and nothing is filed, compared, chosen or written under it. What was
 * missing was anything holding a reader to it — and two readers were not: what orders a block was
 * read off whichever position a walk met last, and where a value declares a block's positions was
 * answered by stopping at the first it does not declare.
 *
 * <p><b>Which is not the same defect a form had.</b> A form's positions are walked to work a bound
 * out at each of them, so the walk decides the answer and what settles it has to be an order the
 * positions themselves give ({@link souther.compiler.numeric.CanonicalOrder}). Every walk of a
 * block ends in an operation that comes to the same thing whichever order it took — a meet, a
 * join, a union, a closure over a relation that is transitive — so there is no order for the block
 * to be asked for, and asking for one would put a question to every vocabulary a relation may be
 * written in that none of them has an answer to. What is wanted here is that it stays that way.
 *
 * <p><b>So the reading is of what a reader of a block does, and the rule is that none of it is
 * positional.</b> A reader may ask whether a block holds a position, how many it holds, walk them
 * into a set, fold them commutatively, or hand what it built to something that takes it as a whole;
 * it may not take the first of them, index them, or read one out by hand. Asked of the reader's
 * whole body rather than of the path from {@code members} to the operation: a walk of a block that
 * is handed to a helper is a reader with nothing positional left in it, which is what this wants to
 * go on saying, and one that keeps the positional read keeps it where this can see it.
 *
 * <p><b>What this does not see.</b> A loop that writes the same local at every turn and reads it
 * after — the shape {@code Confinement#placedAt} had, where what a block is ordered on was
 * whichever position came last — is not a call and is not named below. What sees that shape is the
 * reading behind issue #1760, which is where it was found; this holds the readers to what can be
 * said of them by name.
 */
class NoReaderOfABlockObservesWhichPositionCameFirstTest {

    private static final String THE_BLOCK = "souther/compiler/values/Sameness$Block";

    /**
     * The readers that still take a position out of a block by where it is.
     *
     * <p>None. A reader put here would be one somebody read and found the order could not reach the
     * answer of, which is a fact about that body as it stands rather than about the reader — so it
     * is a place to move rather than a shape to keep.
     */
    private static final List<String> STILL_TO_MOVE = List.of();

    private static final CompiledOutputs COMPILED = CompiledOutputs.ofWhatThisRepositoryPublishes();

    private static final CompiledOutputs AND_WHAT_IS_COMPILED_BESIDE_IT =
            CompiledOutputs.ofEverythingCompiledHere();

    @Test
    void noReaderOfABlockTakesAPositionOutOfItByWhereItIs() {
        assertEquals(STILL_TO_MOVE.stream().sorted().toList(), whoReadsOneByWhereItIs(COMPILED),
                "a block holds its positions in no order, so a reader that takes one of them by"
                        + " where it is has in its answer something the block it read cannot see");
    }

    /**
     * And a reader that does take one is one this finds.
     *
     * <p>The positive control, and the reason there are subjects beside this test. With nobody left
     * to move, a rule that had stopped looking would name nobody and would read as every reader
     * being commutative — the one answer it must not be able to give by accident. So the two shapes
     * that took a position by where it is are written here and the rule is asked of what was
     * compiled beside the test.
     */
    @Test
    void andTheTwoShapesThatDoTakeOneAreBothFound() {
        List<String> found = whoReadsOneByWhereItIs(AND_WHAT_IS_COMPILED_BESIDE_IT);
        String here = ABlockReadByWhereItsPositionsAre.class.getName().replace('.', '/');

        assertTrue(found.contains(here + "#theFirstTheIteratorGives"),
                "a position taken out of a block's walk by hand was not found: " + found);
        assertTrue(found.contains(here + "#theFirstOfThemAsAList"),
                "a position taken out of a block by where it is in a list was not found: " + found);
        assertTrue(found.contains(here + "#theFirstOf"),
                "a position taken by where it is on the far side of a call was not found, so this"
                        + " rule stops holding wherever somebody draws a line through a reader: "
                        + found);
    }

    /**
     * And what a reader is allowed to do is not what this looks for.
     *
     * <p>The negative control. A rule that named every reader of a block would be green only while
     * nobody read one, and the ones written here are what every reader left does: what a block
     * holds walked into a set, asked of every position at once, and handed over whole.
     */
    @Test
    void andTheWaysAReaderMayWalkABlockAreNotFound() {
        List<String> found = whoReadsOneByWhereItIs(AND_WHAT_IS_COMPILED_BESIDE_IT);
        String here = ABlockReadCommutatively.class.getName().replace('.', '/');

        assertEquals(List.of(), found.stream().filter(each -> each.startsWith(here)).toList(),
                "a commutative reading of a block was named as taking a position by where it is,"
                        + " so this rule would refuse the readers it is written to allow");
    }

    /**
     * And the rule was asked of classes that were read.
     *
     * <p>A walk finding no reader of a block would find none taking a position by where it is, and
     * would pass while answering about nothing.
     */
    @Test
    void andTheClassesThatReadABlockWereRead() {
        List<String> reading = new ArrayList<>();
        for (ClassModel read : COMPILED.all()) {
            if (read.methods().stream().anyMatch(NoReaderOfABlockObservesWhichPositionCameFirstTest
                    ::asksABlockForItsPositions)) {
                reading.add(read.thisClass().name().stringValue());
            }
        }

        assertFalse(reading.isEmpty(),
                "nothing here reads a block's positions at all, which is not what this repository"
                        + " holds");
    }

    /**
     * Two readers of a block that take a position by where it is.
     *
     * <p>Written to be found. Nothing calls either and nothing may: what they are for is that the
     * rule above has something to find.
     */
    static final class ABlockReadByWhereItsPositionsAre {

        private ABlockReadByWhereItsPositionsAre() {
        }

        static <A> A theFirstTheIteratorGives(souther.compiler.values.Sameness.Block<A> block) {
            return block.members().iterator().next();
        }

        static <A> A theFirstOfThemAsAList(souther.compiler.values.Sameness.Block<A> block) {
            return List.copyOf(block.members()).getFirst();
        }

        /** And the same read with a line drawn through the middle of it, which is what a rule asked
         *  of one method at a time cannot see. */
        static <A> A theFirstAHelperTakes(souther.compiler.values.Sameness.Block<A> block) {
            return theFirstOf(block.members());
        }

        private static <T> T theFirstOf(java.util.Collection<T> these) {
            return these.iterator().next();
        }
    }

    /**
     * And three that read one the ways a reader may.
     *
     * <p>Written to be passed over, which is what makes the finding above an answer about the shape
     * rather than about anything that mentions a block.
     */
    static final class ABlockReadCommutatively {

        private ABlockReadCommutatively() {
        }

        static <A> Set<A> everyOneOfThem(souther.compiler.values.Sameness.Block<A> block) {
            Set<A> out = new LinkedHashSet<>();
            out.addAll(block.members());
            return out;
        }

        static <A> boolean anyOfThemIs(souther.compiler.values.Sameness.Block<A> block, A wanted) {
            return block.members().stream().anyMatch(each -> each.equals(wanted));
        }

        static <A> int howManyThereAre(souther.compiler.values.Sameness.Block<A> block) {
            return block.members().size();
        }
    }

    /**
     * Every method holding a block's positions that takes one of them by where it is.
     *
     * <p>Holding and not asking: a reader written as {@code first(block.members())} does the same
     * thing as one written in a line, and a rule that asked each method on its own would say the
     * second takes a position by where it is and the first does not
     * ({@link WhoHoldsWhatAReaderHandedOver}).
     */
    private static List<String> whoReadsOneByWhereItIs(CompiledOutputs where) {
        WhoHoldsWhatAReaderHandedOver handed = new WhoHoldsWhatAReaderHandedOver(where);
        List<String> reading = new ArrayList<>();
        for (String holding : handed.holdingWhat(THE_BLOCK, "members")) {
            if (WhoHoldsWhatAReaderHandedOver.takesSomethingByWhereItIs(
                    handed.methodNamed(holding))) {
                reading.add(holding);
            }
        }
        return reading.stream().sorted().distinct().toList();
    }

    /** Whether this method asks a block for the positions it holds. */
    private static boolean asksABlockForItsPositions(MethodModel method) {
        return method.code().stream().flatMap(code -> code.elementStream())
                .anyMatch(element -> element instanceof InvokeInstruction call
                        && call.owner().asInternalName().equals(THE_BLOCK)
                        && call.name().stringValue().equals("members"));
    }

}
