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
     * <p>{@code decidedBy} is what decides that arm, handed over and not left for a naming to work
     * out again from the node. A naming that asked the node what kind of fork it is would answer for
     * the kinds it knows and pass every other straight through, and the arms of a fork it did not
     * know would be ways carrying nothing about which arm was taken. Switched over, a
     * way of deciding an arm that is added to {@link Choice.Decides} is one every naming has to
     * say something about before it compiles.
     */
    P forkArm(Core fork, int part, Choice.Decides decidedBy);

    /** How many arrivals one node is read as before the reading gives up on enumerating them. */
    int mostArrivals();
}
