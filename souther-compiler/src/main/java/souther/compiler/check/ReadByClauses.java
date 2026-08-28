package souther.compiler.check;

import souther.compiler.numeric.OrderedIntervals;
import souther.compiler.values.AdmissibleValues;

import java.util.LinkedHashSet;
import java.util.Set;

/**
 * What the clauses of one value say, with every choice in them decided.
 *
 * <p>The other side of {@link StatedByClauses}, which is the same four things while one question
 * about them is still open: whether each branch of a choice is one anybody can take. That question
 * is answered by working the values out, and until it is answered none of the four has its final
 * form — what the positions admit, where they stop, and what each language is recorded as having
 * taken in are all different for a branch that survives and one that does not.
 *
 * <p><b>So the queries that need the answer live here and nowhere else.</b> A caller holding one of
 * these cannot ask about a branch that has not been decided, because there is no such thing to hold.
 * Held on the planned side as well, a reader could ask what a clause adopted before the branch it
 * was in was known to be dead, and the account would name a rule of a branch nothing satisfies —
 * sending an author to look at something that is not there.
 */
record ReadByClauses(AdmissibleValues<FactSubject> values, OrderedIntervals<FactSubject> ordered,
                     Adoption<FactSubject> byValues, Adoption<FactSubject> byOrder) {

    /**
     * Whether nothing satisfies what has been read.
     *
     * <p>Either language, because each can hold the whole answer on its own: what one of them
     * cannot express it leaves alone.
     */
    boolean holdsNothing() {
        return values.isBottom() || ordered.isBottom();
    }

    /**
     * The positions some reading took the whole of this clause in at.
     *
     * <p>Some, and not both: the two languages are short of different things, and a bound one of
     * them has no word for is read whole by the other. What neither took in is what is left
     * standing.
     */
    Set<FactSubject> adopted() {
        Set<FactSubject> out = new LinkedHashSet<>();
        // Everything either account is about, and not what it put a constraint on: a position a
        // dead branch settled is one the reading answered for and put no constraint on, which is
        // what `took` is asked rather than told.
        byValues.mentions().forEach(each -> {
            if (byValues.took(each)) {
                out.add(each);
            }
        });
        byOrder.mentions().forEach(each -> {
            if (byOrder.took(each)) {
                out.add(each);
            }
        });
        return out;
    }
}
