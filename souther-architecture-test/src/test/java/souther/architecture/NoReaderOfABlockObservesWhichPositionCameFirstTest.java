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
     * What takes a position out of a walk by where it is rather than by what it is.
     *
     * <p>Named by what is called and not by where the call goes, since a reader that does one of
     * these to what it walked out of a block has the order in its answer whatever it does next.
     */
    private static final Set<String> POSITIONAL = Set.of(
            "getFirst", "getLast", "findFirst", "indexOf", "lastIndexOf",
            "limit", "skip", "reduce", "toArray", "listIterator",
            "firstKey", "lastKey", "firstEntry", "lastEntry", "first", "last");

    /**
     * And the walk asked for its first and nothing else, which is the same read written the long
     * way.
     *
     * <p>Read as the two calls next to each other, because a walk of anything asks for an iterator
     * and asks it for what is next: every {@code for (each : these)} there is compiles to exactly
     * those calls, and a rule that named {@code next} would name every reader of a block that walks
     * one at all. What tells the two apart is what stands between them — a walk asks whether there
     * is a next one first, and a reader taking the first asks for it straight away.
     */
    private static boolean asksAWalkForItsFirstAndNothingElse(List<InvokeInstruction> calls) {
        for (int at = 0; at + 1 < calls.size(); at++) {
            if (calls.get(at).name().stringValue().equals("iterator")
                    && calls.get(at + 1).name().stringValue().equals("next")) {
                return true;
            }
        }
        return false;
    }

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

    /** Every method that reads a block's positions and takes one of them by where it is. */
    private static List<String> whoReadsOneByWhereItIs(CompiledOutputs where) {
        List<String> reading = new ArrayList<>();
        for (ClassModel read : where.all()) {
            for (MethodModel each : read.methods()) {
                if (asksABlockForItsPositions(each) && takesOneByWhereItIs(each)) {
                    reading.add(read.thisClass().name().stringValue() + "#"
                            + each.methodName().stringValue());
                }
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

    /**
     * Whether this method takes something out of a walk by where it is.
     *
     * <p>Asked of what the method calls and not of what the block's positions reach. A reader that
     * has one of these in it either does it to what it walked out of a block, which is the defect,
     * or does it to something else while walking a block, which is a reader doing two things and is
     * worth being told about either way.
     */
    private static boolean takesOneByWhereItIs(MethodModel method) {
        List<InvokeInstruction> calls = method.code().stream()
                .flatMap(code -> code.elementStream())
                .filter(InvokeInstruction.class::isInstance)
                .map(InvokeInstruction.class::cast)
                .toList();
        return calls.stream().anyMatch(call -> POSITIONAL.contains(call.name().stringValue())
                        || isReadingAListByIndex(call))
                || asksAWalkForItsFirstAndNothingElse(calls);
    }

    /** {@code get} of a list or of an iterator's place, which a map is asked the same word. */
    private static boolean isReadingAListByIndex(InvokeInstruction call) {
        return call.name().stringValue().equals("get")
                && (call.owner().asInternalName().equals("java/util/List")
                        || call.owner().asInternalName().equals("java/util/ArrayList"));
    }
}
