package souther.compiler.check;

import souther.compiler.numeric.Endpoint;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * Which of the candidates reaching a coordinate account for where it stops.
 *
 * <p><b>What a candidate is is the caller's.</b> A declaration whose clauses are taken away and one
 * authored conjunct taken away are the same three questions asked of different things, and the
 * questions are what is here: whether the candidates moved the end at all, which of them is missed
 * on its own, and which of them holds it alone. Written once per kind of candidate, the second copy
 * would answer the middle question and stop, which is what it did.
 *
 * <p>A candidate reaches here for having been read about the coordinate, which is not the same as having
 * decided anything: a clause reaching a value another clause has already passed moves the end
 * nowhere. So the first question is whether the candidates between them left the coordinate
 * anywhere other than where it would be without every one of them, and only where they did is there
 * a difference for any of them to answer for. Naming them all where there is none does not add a
 * name beside the type's — a line a declaration took in is that declaration's to answer for and no
 * longer the type's ({@code AuthoredLine.obligationOwners}) — it moves the row to an author who can
 * rewrite their clause with the line staying where it is.
 *
 * <p>That first answer is what an instance of this is. It is reached by {@link #read} and by nothing
 * else, so a reader asking which declarations account for an end holds a difference to attribute
 * before the question can be put. The end without the candidates answers whether there is one and
 * answers nothing after: every question below compares a reading against the end the coordinate
 * actually stops at, and a baseline still in reach is a baseline the next comparison can be written
 * against.
 */
final class EndNarrowing<C> {

    /**
     * Where a coordinate stops with some of the candidates taken away.
     *
     * <p>A set, because that is what a counterfactual reading is asked: a candidate named twice is
     * named once, and which order they arrive in is no part of what the reading comes to.
     *
     * <p>An end that is not there is a {@code null}, which is a wider reading and not a missing
     * answer — taking rules away is what widens one.
     */
    interface Ends<C> {
        Endpoint without(Set<C> removed);
    }

    /**
     * Which declarations account for the end, and by which of the questions asked here.
     *
     * <p>The rules are tried in the order they are written below and the first that names anybody is
     * the answer, so what an arm says is which evidence the names came from rather than which of
     * them a world is in. A declaration whose removal moves the end is holding it whatever else is
     * true of it, and there is no reason to go on and ask whether it could hold the end alone.
     */
    sealed interface Answer<C> {

        /** The candidates these are, or none where there are none to name. */
        List<C> names();

        /**
         * The candidates leave the coordinate where it stops without any of them.
         *
         * <p>Not that nothing was written about it. Their clauses were read and reached a value
         * something else had already stopped it at, and an author sent here would be sent to a
         * clause they can rewrite with the end staying put.
         */
        record NoNarrowing<C>() implements Answer<C> {

            @Override
            public List<C> names() {
                return List.of();
            }
        }

        /**
         * Each of these moves the end when it alone is taken away, the rest left as they are.
         *
         * @param names in declaration order
         */
        record Indispensable<C>(List<C> names) implements Answer<C> {}

        /**
         * None of them is missed on its own and each of these leaves the end where it is with the
         * rest of the candidates gone.
         *
         * <p>Two or more saying what the edge says, which is not a reason to name one of them over
         * the others and not a reason to name a candidate that says something short of it.
         *
         * @param names in declaration order
         */
        record AloneSufficient<C>(List<C> names) implements Answer<C> {}

        /**
         * The candidates moved the end and neither question told any of them apart.
         *
         * <p>What is known is that the set as a whole accounts for the end, and this is that and not
         * an answer that every one of them does. A bound can arrive along a path through the
         * differences where clauses reach an end only together, and the set is handed over as what
         * these counterfactuals came to rather than as a finding about each declaration in it.
         *
         * @param names in declaration order
         */
        record Undifferentiated<C>(List<C> names) implements Answer<C> {}
    }

    private final Endpoint end;

    private final List<C> candidates;

    private final Ends<C> ends;

    private final java.util.Comparator<C> order;

    private EndNarrowing(Endpoint end, List<C> candidates, Ends<C> ends,
                         java.util.Comparator<C> order) {
        this.end = end;
        this.candidates = candidates;
        this.ends = ends;
        this.order = order;
    }

    /**
     * What the candidates account for at {@code end}, which is nothing unless they moved it there.
     *
     * @param end        where the coordinate stops with every clause read, which is an end that is
     *                   there: a coordinate nothing stops on this side has no end for a declaration
     *                   to have moved anywhere, and a caller with none has its answer already
     * @param candidates the declarations that wrote a relation about it, in the order they were
     *                   found
     * @param ends       the same coordinate read again with rules taken away
     */
    static <C extends Comparable<? super C>> Answer<C> read(Endpoint end, List<C> candidates,
                                                            Ends<C> ends) {
        return read(end, candidates, ends, java.util.Comparator.naturalOrder());
    }

    /**
     * The same, where what a candidate is has no order of its own for the caller to leave unsaid.
     *
     * @param order the one order these are answered in, which is the caller's to say: what a line
     *              is told apart by is the answer, so an order read off the walk that collected the
     *              candidates would make two readings of one edge into two lines
     */
    static <C> Answer<C> read(Endpoint end, List<C> candidates, Ends<C> ends,
                              java.util.Comparator<C> order) {
        return end.sameAs(ends.without(Set.copyOf(candidates)))
                ? new Answer.NoNarrowing<>()
                : new EndNarrowing<>(end, candidates, ends, order).attribute();
    }

    private Answer<C> attribute() {
        List<C> indispensable = new ArrayList<>();
        for (C each : candidates) {
            if (!end.sameAs(ends.without(Set.of(each)))) {
                indispensable.add(each);
            }
        }
        if (!indispensable.isEmpty()) {
            return new Answer.Indispensable<>(inOrder(indispensable));
        }
        List<C> alone = new ArrayList<>();
        for (C each : candidates) {
            if (end.sameAs(ends.without(allBut(each)))) {
                alone.add(each);
            }
        }
        if (!alone.isEmpty()) {
            return new Answer.AloneSufficient<>(inOrder(alone));
        }
        return new Answer.Undifferentiated<>(inOrder(candidates));
    }

    private Set<C> allBut(C kept) {
        Set<C> removed = new LinkedHashSet<>(candidates);
        removed.remove(kept);
        return removed;
    }

    /**
     * In one order, whoever found them. Several of these are one answer and the answer is what a
     * line is told apart by, so an order read off the walk that collected them would make two
     * readings of one edge into two lines.
     *
     * <p>Which order that is belongs to whoever knows what a candidate is. For declarations it is
     * the declaration's own order and not its name alone: two of them holding one end can be
     * written in two modules — an inner record's clause and an outer record's reaching the same
     * coordinate at the same value — and two modules may each declare a {@code Span}, so a name is
     * not what tells those two apart.
     */
    private List<C> inOrder(List<C> found) {
        return found.stream().sorted(order).toList();
    }
}
