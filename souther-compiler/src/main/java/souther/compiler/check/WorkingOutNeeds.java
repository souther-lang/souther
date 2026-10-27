package souther.compiler.check;

import java.util.ArrayList;
import java.util.List;

/**
 * What a run needs of the numbers to get through working a clause out, and whether that is all of it.
 *
 * <p>The bounds a clause comes to are the clause over the whole numbers, and a run works it out over
 * the numbers a type holds: an operator answers only on some operands. Two things are known of that,
 * and neither is the other's absence. {@code asked} is what the operators ask of their operands
 * where it could be said as relations. {@code read} is whether every operator the clause may work
 * out is in it — an operator no region is written for, a product of two values, and an operator on a
 * side of a choice that is not reached wherever the clause is, are the ones that are not.
 *
 * <p>So an empty {@code asked} is two answers. With {@code read} it is that nothing is asked, and
 * the bounds are the whole of the clause; without it, that nothing could be said, and they are not
 * known to be.
 *
 * @param asked the relations the operands must hold for every operator read to answer, less what
 *              was already held where they were read
 * @param read  whether every operator the clause may work out is among them
 * @param bindingsRead whether every operator in the value a binding of the clause is given is
 *              among them. A binding's value is worked out whether or not the clause reads its
 *              name, so an operator there is one the clause's statements do not account for
 */
record WorkingOutNeeds(List<NumericConstraint> asked, boolean read, boolean bindingsRead) {

    /** A clause working nothing out that can stop a run. */
    static final WorkingOutNeeds NONE = new WorkingOutNeeds(List.of(), true);

    /** A clause some operator of which may stop a run where nothing says. */
    static final WorkingOutNeeds UNREAD = new WorkingOutNeeds(List.of(), false);

    WorkingOutNeeds {
        asked = List.copyOf(asked);
    }

    /** What a clause needs where every binding's value it holds, if any, was read. */
    WorkingOutNeeds(List<NumericConstraint> asked, boolean read) {
        this(asked, read, true);
    }

    /** What both of two clauses need, which a run working one out then the other needs together. */
    WorkingOutNeeds and(WorkingOutNeeds other) {
        List<NumericConstraint> both = new ArrayList<>(asked);
        both.addAll(other.asked);
        return new WorkingOutNeeds(both, read && other.read, bindingsRead && other.bindingsRead);
    }

    /**
     * This, under a binding whose value was worked out and was {@code valueRead} or was not.
     *
     * <p>What the value needs is in {@link #asked} by {@link #and}; this says where an operator
     * the value holds that was not read stands, so that a caller attributing {@code read} to the
     * statements of the clause can tell the two apart.
     */
    WorkingOutNeeds underABindingWhoseValue(boolean valueRead) {
        return new WorkingOutNeeds(asked, read, bindingsRead && valueRead);
    }

    /**
     * What this needs where it is worked out only on some runs, and not on every one that reaches
     * the clause.
     *
     * <p>Not asked of the operands it asks of, since the runs that skip it do not stop there. What
     * is lost is said: unless nothing is asked of it and all of it was read, it is not known to be
     * all of it.
     */
    WorkingOutNeeds onlyOnSomeRuns() {
        return asked.isEmpty() && read ? this
                : new WorkingOutNeeds(List.of(), false, bindingsRead);
    }
}
