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
 */
record WorkingOutNeeds(List<NumericConstraint> asked, boolean read) {

    /** A clause working nothing out that can stop a run. */
    static final WorkingOutNeeds NONE = new WorkingOutNeeds(List.of(), true);

    /** A clause some operator of which may stop a run where nothing says. */
    static final WorkingOutNeeds UNREAD = new WorkingOutNeeds(List.of(), false);

    WorkingOutNeeds {
        asked = List.copyOf(asked);
    }

    /** What both of two clauses need, which a run working one out then the other needs together. */
    WorkingOutNeeds and(WorkingOutNeeds other) {
        List<NumericConstraint> both = new ArrayList<>(asked);
        both.addAll(other.asked);
        return new WorkingOutNeeds(both, read && other.read);
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
        return asked.isEmpty() && read ? this : UNREAD;
    }
}
