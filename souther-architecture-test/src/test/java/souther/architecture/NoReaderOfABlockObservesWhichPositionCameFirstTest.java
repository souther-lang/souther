package souther.architecture;

import org.junit.jupiter.api.Test;

import java.lang.classfile.ClassModel;
import java.lang.classfile.MethodModel;
import java.lang.classfile.instruction.InvokeInstruction;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
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
     * Every reader that reads a block's positions for where they are, and what was found when it
     * was read.
     *
     * <p><b>A closed set, which is what makes this a guard rather than a list of words.</b> What is
     * looked for is a reader that enumerates a value holding no order and comes to something whose
     * own equality sees one — a sequence, a text, a position taken by where it is. Some of those
     * readers are fine, and which ones is not a thing a rule can read off a name: it is a fact
     * about the body, and the fact is written down here once instead of being re-established
     * whenever somebody wonders.
     *
     * <p>So a reader reaching this rule is red until somebody reads it and says which of the two it
     * is. What must not happen is a name added here without that reading — which is why each of
     * them says what was found rather than that it is allowed.
     */
    private static final Map<String, String> READ_AND_SETTLED = Map.ofEntries(
            Map.entry("souther/compiler/check/ProofOfEmptiness#declaredIn"
                            + "(Ljava/util/Set;Ljava/util/SequencedMap;)Ljava/util/List;",
                    "the positions are gathered into a set that holds no order, and the sequence"
                            + " handed back is walked out of the positions the value declares"),
            Map.entry("souther/compiler/check/ProofOfEmptiness#declared"
                            + "(Lsouther/compiler/values/Sameness$Block;Ljava/util/Map;)"
                            + "Ljava/util/List;",
                    "what comes back is the ordinals the value gives the positions, sorted — so the"
                            + " walk decides which numbers are in it and nothing about their"
                            + " order"),
            Map.entry("souther/compiler/values/Reached#at"
                            + "(Lsouther/compiler/values/Sameness$Block;)"
                            + "Lsouther/compiler/values/AdmittedPlan;",
                    "the sequence is handed straight to a meet over the plans in it, which comes to"
                            + " the same plan whichever order they are met in"),
            Map.entry("souther/compiler/values/Refinement#of"
                            + "(Lsouther/compiler/values/Sameness;Lsouther/compiler/values/"
                            + "Sameness;)Lsouther/compiler/values/Refinement;",
                    "the positions gathered are what a refusal names, and it names them in one"
                            + " order (InOneOrder) rather than in the order the walk reached them"),
            Map.entry("souther/compiler/values/AdmittedPlan#held"
                            + "(Ljava/util/Set;Ljava/lang/String;)Ljava/util/Set;",
                    "the parts are put in the order a plan itself decides (PlanOrder) before"
                            + " anything is built from them, so what a walk handed in cannot reach"
                            + " the answer"),
            Map.entry("souther/compiler/values/AdmittedPlan#flattened"
                            + "(Ljava/util/List;Z)Ljava/util/List;",
                    "what it hands back is poured into a set by both its callers and then put in"
                            + " the plan's own order, so the sequence it keeps is one nothing"
                            + " reads"),
            Map.entry("souther/compiler/values/Standing#across(Ljava/util/Set;)Ljava/util/List;",
                    "the positions are asked for membership and nothing else; what comes back is"
                            + " every reason once in the order the rules were written, which the"
                            + " entries carry"),
            Map.entry("souther/compiler/values/Standing#<init>(Ljava/util/List;Ljava/util/Set;)V",
                    "the entries are the rules in the order they were written and the positions are"
                            + " a set asked for membership, so neither is read for where anything"
                            + " came"),
            Map.entry("souther/compiler/values/AdmissibleValues#unreadAffecting"
                            + "(Ljava/lang/Object;)Ljava/util/List;",
                    "the positions are handed on to be asked for membership, and what comes back is"
                            + " every reason once in the order the parts of the clause were met"),
            // The two below hand a walk back and are read for that reason, and what they hand back
            // is a set: two of them are one set wherever they hold the same things, so the order
            // either was filled in is not in the answer.
            Map.entry("souther/compiler/values/Sameness#holding"
                            + "(Lsouther/compiler/values/Sameness$Block;)Ljava/util/Set;",
                    "what comes back is the blocks holding those positions, as a set — one set"
                            + " however the positions were walked to reach them"),
            Map.entry("souther/compiler/values/Apartness#partsOf"
                            + "(Lsouther/compiler/values/Sameness$Block;"
                            + "Lsouther/compiler/values/Sameness;)Ljava/util/Set;",
                    "what comes back is the parts that block is made of, as a set — one set however"
                            + " the positions were walked to reach them"));

    private static final CompiledOutputs COMPILED = CompiledOutputs.ofWhatThisRepositoryPublishes();

    private static final CompiledOutputs AND_WHAT_IS_COMPILED_BESIDE_IT =
            CompiledOutputs.ofEverythingCompiledHere();

    @Test
    void everyReaderThatReadsABlockForWhereItsPositionsAreHasBeenRead() {
        assertEquals(READ_AND_SETTLED.keySet().stream().sorted().toList(),
                whoReadsOneByWhereItIs(COMPILED),
                "a block holds its positions in no order, so a reader whose answer sees the order"
                        + " it walked has in it something the block it read cannot — each of them"
                        + " is read and settled above, and one that is not is one nobody has read");
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

        assertTrue(isAmong(found, here, "theFirstTheIteratorGives"),
                "a position taken out of a block's walk by hand was not found: " + found);
        assertTrue(isAmong(found, here, "theFirstOfThemAsAList"),
                "a position taken out of a block by where it is in a list was not found: " + found);
        assertTrue(isAmong(found, here, "intoASequence"),
                "a walk poured into a sequence by a collection this rule does not name was not"
                        + " found, so what it looks for is how the answer was built rather than"
                        + " what the answer is: " + found);
        assertTrue(isAmong(found, here, "oneOf"),
                "a position taken by where it is inside a helper that shares its name with one"
                        + " taking no walk was not found, so a method of that name is being read"
                        + " for another of the same name: " + found);
        assertTrue(isAmong(found, here, "theFirstOf"),
                "a position taken by where it is on the far side of a call was not found, so this"
                        + " rule stops holding wherever somebody draws a line through a reader: "
                        + found);
    }

    /**
     * And a reading that comes to an answer with no walk in it is not what this looks for.
     *
     * <p>The negative control. A rule that named every reader of a block would be green only while
     * nobody read one, and the ones written here are what a reader may do without anybody having
     * to read the body: ask whether a position is among them, and ask how many there are.
     *
     * <p><b>Handing a walk back is not one of those, however commutative the walk was.</b> What a
     * method says it hands back is not what it hands back — a method giving a {@code Collection}
     * gives whatever it built — so a reader that hands one over is read and settled above rather
     * than passed over here on the strength of a declared type. {@code everyOneOfThem} beside them
     * is such a reader, and it is where the rule can see it.
     */
    @Test
    void andAReadingThatKeepsNoWalkInItsAnswerIsNotFound() {
        List<String> found = whoReadsOneByWhereItIs(AND_WHAT_IS_COMPILED_BESIDE_IT);
        String here = ABlockReadCommutatively.class.getName().replace('.', '/');

        assertEquals(List.of(),
                found.stream().filter(each -> each.startsWith(here + "#anyOfThemIs(")
                        || each.startsWith(here + "#howManyThereAre(")).toList(),
                "a reading of a block that comes to an answer holding no walk was named as reading"
                        + " one for where its positions are, so this rule would refuse the readers"
                        + " it is written to allow");
    }

    /** Whether one of {@code found} is this method, which is named by what it takes as well as by
     *  what it is called — two methods of one name are two methods. */
    private static boolean isAmong(List<String> found, String owner, String called) {
        return found.stream().anyMatch(each -> each.startsWith(owner + "#" + called + "("));
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

        /** And the same again where the helper shares its name with one that takes no walk, which
         *  is what a rule keyed on the name alone cannot tell apart. */
        static <A> A theFirstAnOverloadTakes(souther.compiler.values.Sameness.Block<A> block) {
            return oneOf(block.members());
        }

        private static <T> T oneOf(java.util.Collection<T> these) {
            return these.iterator().next();
        }

        /** Named as the one above and taking no walk at all. Written so that a rule keyed on the
         *  name has two methods to choose between and may choose this one. */
        static String oneOf(int number) {
            return String.valueOf(number);
        }

        /** And a sequence handed back that was built by nothing this rule names and handed back as
         *  a kind of list nothing names either. Written so that what the rule looks for is what the
         *  answer is rather than what it is called or how it was made. */
        static <A> List<A> theSequenceAHelperMakes(souther.compiler.values.Sameness.Block<A> block) {
            return intoASequence(block.members());
        }

        private static <T> java.util.concurrent.CopyOnWriteArrayList<T> intoASequence(
                java.util.Collection<T> these) {
            return new java.util.concurrent.CopyOnWriteArrayList<>(these);
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
        WhoHoldsWhatAReaderHandedOver handed = WhoHoldsWhatAReaderHandedOver.of(where);
        List<String> reading = new ArrayList<>();
        for (String holding : handed.holdingWhat(THE_BLOCK, "members")) {
            if (handed.readsAWalkForWhereThingsAre(handed.methodThatIs(holding))) {
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
