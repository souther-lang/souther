package souther.architecture;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A reader that walks a form's positions asks the atom domain what order to walk them in.
 *
 * <p>A {@link souther.compiler.numeric.CanonicalForm} is a mapping and holds no order of its own.
 * Two writings of one rule are one form, and which of them a caller typed is not something the form
 * kept — so a reader that walks the positions as the mapping hands them over has an order in its
 * answer that the form it read cannot see, and two callers that wrote one rule two ways are
 * answered two ways.
 *
 * <p><b>Which is why the walk is a question about the atom domain.</b> {@code entriesIn} and
 * {@code atomsIn} take a {@link souther.compiler.numeric.CanonicalOrder}, the domain says what its
 * own is, and a pair of positions that order cannot tell apart is refused rather than walked as one.
 * What is left of {@code coefs()} is what a mapping answers: what a position weighs, whether the
 * form names one, and how many there are.
 *
 * <p><b>Asked of what a reader takes by where it is, and not of whether it walks at all.</b> A walk
 * whose answer is a sum, a union or a conjunction comes to the same thing whichever order it took,
 * and a rule naming every walk would be a rule about how a fold is spelled. What cannot come to the
 * same thing is a reader that takes a position out of the walk by where it is — the first of them,
 * one by its index, the one an iterator hands over straight away — so that is what is named, in the
 * words {@link WhoHoldsWhatAReaderHandedOver} names it for a block.
 *
 * <p><b>And asked of every method the mapping reaches, not of the one that asked for it.</b> A
 * reader written as {@code firstOf(form.coefs())} takes the same position the same way as one
 * written in a line; a rule asked of each method on its own sees neither half of it, and extracting
 * a helper is what happens to a walk that is written twice.
 *
 * <p><b>Every one of those is something to close and not a shape to keep.</b> The list below is
 * what is still to move, and a reader taken off it is one fewer place where the order a form does
 * not hold can start being read again.
 */
class AFormIsWalkedThroughTheOrderItsPositionsDecideTest {

    private static final String THE_FORM = "souther/compiler/numeric/CanonicalForm";

    /**
     * Every reader that walks a form's coefficients into something whose answer sees the order, and
     * what was found when it was read.
     *
     * <p>Every walk of a form's positions asks the atom domain for the order it takes them in, so
     * what is left here is a reader whose answer happens to be a sequence and whose sequence was
     * not decided by a walk. A reader reaching this rule is red until somebody reads it and says
     * which it is — that, or a walk whose answer has the order in it and has to move.
     */
    private static final Map<String, String> READ_AND_SETTLED = Map.of(
            "souther/compiler/numeric/AffineReduction#sidedBy"
                    + "(Lsouther/compiler/numeric/AffineConstraint$Disequality;"
                    + "Lsouther/compiler/numeric/FormReach;)Ljava/util/List;",
            "what it hands back holds at most one half-space, and which one is settled by which"
                    + " side of the value the sum is proved to lie rather than by any walk",
            "souther/compiler/numeric/FormReach#apartFrom(Ljava/util/Map;)Ljava/util/Set;",
            "what it hands back is a set of premises by identity, asked only whether a premise is"
                    + " in it, and whether one is turns on whether it names any of the form's"
                    + " positions, which no order of them changes");

    private static final CompiledOutputs COMPILED = CompiledOutputs.ofWhatThisRepositoryPublishes();

    private static final CompiledOutputs AND_WHAT_IS_COMPILED_BESIDE_IT =
            CompiledOutputs.ofEverythingCompiledHere();

    /**
     * Every reader the rule finds is one still to move, and every one still to move is found.
     *
     * <p>Equal and not contained, which is also what says the rule was asked of classes that read a
     * form: the list above is not empty, so a walk that read no reader of a form would find none
     * and fail here rather than pass while answering about nothing.
     */
    @Test
    void everyReaderThatWalksAFormsPositionsIsOneOfTheOnesStillToMove() {
        assertEquals(READ_AND_SETTLED.keySet().stream().sorted().toList(), whoWalksAForm(COMPILED),
                "a reader that walks a form's positions as the mapping hands them over has an"
                        + " order in its answer that the form cannot see — it asks the atom domain"
                        + " for one (CanonicalForm#entriesIn), or it is named above with why the"
                        + " order cannot reach what it answers");
    }

    /**
     * And a reader that does take the walk is one this finds.
     *
     * <p>The positive control, and the reason there is a subject beside this test. With nobody left
     * to move, a rule that had stopped looking for anything would name nobody and would read as
     * every reader having moved — which is the one answer it must not be able to give by accident.
     * So one reader that walks a form is compiled here, and the rule is asked of what was compiled
     * beside the test as well as of what this repository publishes.
     */
    @Test
    void andAReaderThatDoesTakeTheWalkIsOneThisFinds() {
        List<String> found = whoWalksAForm(AND_WHAT_IS_COMPILED_BESIDE_IT);

        String here = AFormWalkedAsItIsHeld.class.getName().replace('.', '/');

        assertTrue(isAmong(found, here, "positionsAsTheyCome"),
                "the one reader written here to walk a form as it is held was not found, so what"
                        + " this rule looks for is not what such a reader does: " + found);
        assertTrue(isAmong(found, here, "asItComes"),
                "a form walked as it is held on the far side of a call was not found, so this rule"
                        + " stops holding wherever somebody draws a line through a reader: " + found);
    }

    /** Whether one of {@code found} is this method, which is named by what it takes as well as by
     *  what it is called — two methods of one name are two methods. */
    private static boolean isAmong(List<String> found, String owner, String called) {
        return found.stream().anyMatch(each -> each.startsWith(owner + "#" + called + "("));
    }

    /**
     * And every place the walk is allowed to stop is a place there is.
     *
     * <p>A boundary named by something that no longer exists is one nothing stops at, and the rule
     * would run through whatever stands there now and report its reading of its own answer. So the
     * names are held against what was compiled.
     */
    @Test
    void andEveryPlaceTheWalkStopsAtIsOneThatExists() {
        assertEquals(Set.of(),
                WhoHoldsWhatAReaderHandedOver.of(AND_WHAT_IS_COMPILED_BESIDE_IT)
                        .boundariesThatAreNotThere(),
                "a walk stops at each of these because of what it promises there, and a name with"
                        + " nothing under it promises nothing");
    }

    /**
     * A reader of a form that takes its positions as the mapping hands them over.
     *
     * <p>Written to be found. Nothing calls it and nothing may: what it is for is that the rule
     * above has something to find, so that finding nothing in what this repository publishes is an
     * answer about the readers rather than about the rule.
     */
    static final class AFormWalkedAsItIsHeld {

        private AFormWalkedAsItIsHeld() {
        }

        static <A> A positionsAsTheyCome(souther.compiler.numeric.CanonicalForm<A> form) {
            return List.copyOf(form.coefs().keySet()).getFirst();
        }

        /** And the same read with a line drawn through the middle of it, which is what a rule asked
         *  of one method at a time cannot see. */
        static <A> A theFirstAHelperTakes(souther.compiler.numeric.CanonicalForm<A> form) {
            return asItComes(form.coefs());
        }

        private static <K, V> K asItComes(java.util.Map<K, V> coefs) {
            return coefs.keySet().iterator().next();
        }
    }

    /**
     * Every method holding a form's coefficients that walks what it was handed.
     *
     * <p>Holding and not asking: a reader written as {@code asTheyCome(form.coefs())} takes the
     * walk the mapping happens to give as surely as one that writes it in a line, and a rule asked
     * of each method on its own would see neither half of it
     * ({@link WhoHoldsWhatAReaderHandedOver}).
     */
    private static List<String> whoWalksAForm(CompiledOutputs where) {
        WhoHoldsWhatAReaderHandedOver handed = WhoHoldsWhatAReaderHandedOver.of(where);
        List<String> walking = new ArrayList<>();
        for (String holding : handed.holdingWhat(THE_FORM, "coefs")) {
            if (handed.readsAWalkForWhereThingsAre(handed.methodThatIs(holding))) {
                walking.add(holding);
            }
        }
        return walking.stream().sorted().distinct().toList();
    }
}
