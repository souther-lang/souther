package souther.compiler.flow;

import souther.compiler.check.Choice;
import souther.compiler.check.ScopeStep;
import souther.compiler.core.Core;

/**
 * How a reading writes down what got a run to a value.
 *
 * <p>The one part of {@link ValueArrivals} that differs between its readers, and the only part. A
 * naming decides what a path is written as and which conditions it has words for; it decides nothing
 * about whether an expression arrives or about what a value comes to. Those are read off the body,
 * and a naming that could move them would be the numbering deciding what the body does — which is
 * what happened when a comparison the numbering could not place was answered as a comparison with no
 * value.
 *
 * <p>So: a naming reaches {@link Paths} and reaches nothing else. It may write the conditions
 * differently, it may turn a {@link Completeness#COMPLETE} path into a {@link Completeness#PARTIAL}
 * one, it may leave out a way it can see no run takes, and it may decline to hold more ways apart
 * than it will. What none of that touches is {@link Comes}, which is computed with no naming at all —
 * so this is a structure rather than a claim, and there is nothing here for a test to catch.
 *
 * <p>{@code P} is a value. Two of them that stand for the same way are equal, because that is what
 * makes a way found twice one way rather than two.
 */
public interface Naming<P> {

    /** The path with nothing settled on it, which is what a value nothing forks arrives by. */
    P nowhere();

    /**
     * Both sets of conditions, or null where between them they settle one decision two ways.
     *
     * <p>Null is no path and not an unnamed one: a run that took the first cannot have taken the
     * second, so there is nothing here to name.
     */
    P join(P held, P more);

    /**
     * The naming a child is read in, {@code step} being the way from its parent into it, which may
     * have words for a name the step binds.
     *
     * <p>Every step and not a chosen few. What a name means changes where a tree's names are read
     * under a new scope ({@link ScopeStep}), and a naming that entered some of those steps and not
     * others would answer under a binding and stay outside an attempt's {@code then} — a name
     * meaning one thing to the reading that found the positions and another to this.
     */
    Naming<P> entering(ScopeStep step);

    /**
     * That {@code value} came out {@code held}, or null where this naming has no words for it.
     *
     * <p>Null does not stop the value being read. A value this cannot place still comes out the way
     * it comes out; what is missing is a way to say so, and the path carrying it is
     * {@link Completeness#PARTIAL} rather than absent.
     *
     * <p>Any value the reading worked a truth out for, which is not only a comparison: a position of
     * the input holding a truth comes out both ways too. A naming with words for one shape and not
     * the other answers null for the other, which costs the path its completeness and costs the
     * reading nothing.
     */
    P side(Core value, boolean held);

    /** That a run took case {@code part} of {@code match}, or null where this has no words for it. */
    P matchCase(Core.Match match, int part);

    /**
     * That a run took arm {@code part} of {@code fork}, said of the fork itself, or null.
     *
     * <p>What decides the arm is {@link Choice#decidingArm}'s answer, and a naming switches over it
     * rather than asking the node what kind of fork it is. Asked of the node, a naming answers for
     * the kinds it knows and passes every other straight through, and the arms of a fork it did not
     * know are ways carrying nothing about which arm was taken. Switched over, a way of deciding an
     * arm added to {@link Choice.Decides} is one every naming has to say something about before it
     * compiles.
     */
    P forkArm(Core fork, int part);

    /**
     * {@code onlyWay} as a run that went down arm {@code part} of {@code fork} is seen taking it,
     * written down whole, or null where this naming has no words for that.
     *
     * <p>Asked only where {@code onlyWay} is the one way the condition may come out the way into
     * the arm, so a run seen at the arm is a run seen having come that way and the condition having
     * come out the arm's way. That is what lets the arm stand for a condition no construct of its
     * own records — a truth the body was handed comes out a way at no comparison, and the arm the
     * fork takes on it is where a run is seen. Where the condition may come out that way by two
     * ways the arm cannot say which, and this is not asked.
     *
     * <p>The way and not a second account beside it. Where the reading worked out the value
     * {@code onlyWay} comes to, what the condition settled is what the way says, and the arm adds
     * where a run through it is seen; a way already written down whole and seen wherever it is seen
     * needs nothing of the arm, and is answered as it is. Where the reading could not work out the
     * value, the way says nothing of the condition coming out the arm's way, and that is the arm's
     * to add.
     */
    P seenAtTheArm(Core.If fork, int part, Arrival<P> onlyWay);

    /**
     * {@code way}, one of the ways the condition comes out into arm {@code part} of {@code fork},
     * as a run down the arm is seen taking it.
     *
     * <p>Asked where there may be others, so the arm cannot stand for this way — a run down it may
     * have come by any of them. What it can add is to what the way already says of itself: a way
     * that says an operand was not run says something only where the operator was, and taking an
     * arm of a fork whose condition runs the operator first says it was.
     */
    P oneOfTheWaysIn(Core.If fork, int part, P way);

    /**
     * {@code left}, the one way the left of {@code operator} goes on, as a run that went on into the
     * right and came out {@code right} is seen taking it.
     *
     * <p>The right runs only where the left went on, so where a run through the right is recorded
     * is where a run is seen having come by the left's one way.
     */
    P wentOn(Core.Binary operator, P left, Arrival<P> right);

    /**
     * {@code left}, the one way the left of {@code operator} settles its answer, as a run that
     * stopped there without running the right is seen taking it.
     */
    P stoppedShort(Core.Binary operator, P left);

    /** How many arrivals one node is read as before the reading gives up on enumerating them. */
    int mostArrivals();
}
