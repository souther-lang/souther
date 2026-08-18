package souther.compiler.check;

import org.junit.jupiter.api.Test;

import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A choice reads the rule and not the tree it is written as.
 *
 * <p>{@code (a || b) || c} and {@code a || (b || c)} are one rule, so what a report says of them is
 * one thing. That is a property of the composition rather than of any one clause, which is why it is
 * held here and not by a pair of models: a rule whose alternatives happen to be settled by some
 * third reading would pass either way, and the property would go untested.
 *
 * <p>What it rests on is that a constraint and an answer are two things. A constraint is open to
 * being widened by an alternative nothing could read — a value satisfying that branch owes this one
 * nothing — and "this clause imposes nothing here", which is what a branch admitting nothing leaves,
 * is not: a further choice imposes nothing either. Held as one, whether the second survived turned
 * on where the brackets fell.
 */
class AChoiceReadsTheRuleAndNotTheTreeItIsWrittenAsTest {

    /** A branch nothing could read, about `x`. */
    private static final Adoption<String> UNREAD = Adoption.at(Set.of("x"), Set.of(), true);

    /** A branch read whole, about `y`. */
    private static final Adoption<String> READ = Adoption.at(Set.of("y"), Set.of("y"), false);

    /**
     * One alternative and whether anything satisfies it, composed the way
     * {@link StatedByClauses#either} composes them.
     *
     * <p>Whether a branch admits nothing is the state's to know and not the evidence's, so it is
     * carried beside here. A choice is dead where every alternative is, which is the rule the states
     * are composed by.
     */
    private record Branch(Adoption<String> adoption, boolean dead) {

        Branch or(Branch other) {
            if (dead && other.dead) {
                return new Branch(adoption.bothDead(other.adoption), true);
            }
            if (dead) {
                return new Branch(other.adoption.beside(adoption), false);
            }
            if (other.dead) {
                return new Branch(adoption.beside(other.adoption), false);
            }
            return new Branch(adoption.either(other.adoption), false);
        }
    }

    private static final Branch UNREADABLE = new Branch(UNREAD, false);
    private static final Branch IMPOSSIBLE = new Branch(READ, true);

    /**
     * Three alternatives compose the same whichever way the brackets fall.
     *
     * <p>The shape that broke it: two branches nothing could read beside one that admits nothing.
     * Grouped one way the dead branch met a choice that had already given up, and grouped the other
     * it met the unread branch afterwards — which widened a position the dead branch had settled,
     * because settling was being kept as though it were a constraint.
     */
    @Test
    void aChoiceOfThreeComposesTheSameWhicheverWayItIsBracketed() {
        Branch left = UNREADABLE.or(UNREADABLE).or(IMPOSSIBLE);
        Branch right = UNREADABLE.or(UNREADABLE.or(IMPOSSIBLE));

        assertEquals(left.adoption().took("y"), right.adoption().took("y"),
                "the position the branch that admits nothing named");
        assertEquals(left.adoption().took("x"), right.adoption().took("x"),
                "and the one the unread branches were about");
        assertTrue(left.adoption().took("y"),
                "which is settled: nothing satisfies the branch that named it, so the choice"
                        + " imposes nothing there");
        assertFalse(left.adoption().took("x"),
                "while nothing read what the choice does to this one");
    }

    /** And the same whichever order the branches are met in, which is the other thing a walk can
     *  vary. */
    @Test
    void andTheSameWhicheverOrderTheBranchesAreMetIn() {
        assertEquals(UNREADABLE.or(UNREADABLE).or(IMPOSSIBLE).adoption().took("y"),
                IMPOSSIBLE.or(UNREADABLE).or(UNREADABLE).adoption().took("y"));
    }

    /**
     * A constraint is still widened by an alternative nothing could read.
     *
     * <p>The half that has to keep working. Settling is not a constraint and a constraint is not
     * settling: a value satisfying the unread branch owes the read one nothing, so what that branch
     * said of its position binds nothing.
     */
    @Test
    void aConstraintIsStillWidenedByAnUnreadAlternative() {
        assertFalse(READ.either(UNREAD).took("y"),
                "what the read branch said of `y` binds nothing where the other can be taken");
        assertTrue(READ.both(UNREAD).took("y"),
                "and a conjunct nothing read leaves the one beside it saying what it said");
    }
}
