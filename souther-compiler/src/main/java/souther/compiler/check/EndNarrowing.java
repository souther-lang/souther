package souther.compiler.check;

import souther.compiler.numeric.Endpoint;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * Which of the declarations relating a coordinate to something else account for where it stops.
 *
 * <p>A declaration reaches here for having written such a relation, which is not the same as having
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
final class EndNarrowing {

    /**
     * Where a coordinate stops with the clauses of some declarations taken away.
     *
     * <p>A set, because that is what a counterfactual reading is asked: a declaration named twice is
     * named once, and which order they arrive in is no part of what the reading comes to.
     *
     * <p>An end that is not there is a {@code null}, which is a wider reading and not a missing
     * answer — taking clauses away is what widens one.
     */
    interface Ends {
        Endpoint without(Set<TypeSymbol.AtModule> removed);
    }

    /**
     * Which declarations account for the end, and by which of the questions asked here.
     *
     * <p>The rules are tried in the order they are written below and the first that names anybody is
     * the answer, so what an arm says is which evidence the names came from rather than which of
     * them a world is in. A declaration whose removal moves the end is holding it whatever else is
     * true of it, and there is no reason to go on and ask whether it could hold the end alone.
     */
    sealed interface Answer {

        /** The declarations these names are, or none where there are none to name. */
        List<TypeSymbol.AtModule> names();

        /**
         * The candidates leave the coordinate where it stops without any of them.
         *
         * <p>Not that nothing was written about it. Their clauses were read and reached a value
         * something else had already stopped it at, and an author sent here would be sent to a
         * clause they can rewrite with the end staying put.
         */
        record NoNarrowing() implements Answer {

            @Override
            public List<TypeSymbol.AtModule> names() {
                return List.of();
            }
        }

        /**
         * Each of these moves the end when it alone is taken away, the rest left as they are.
         *
         * @param names in declaration order
         */
        record Indispensable(List<TypeSymbol.AtModule> names) implements Answer {}

        /**
         * None of them is missed on its own and each of these leaves the end where it is with the
         * rest of the candidates gone.
         *
         * <p>Two or more saying what the edge says, which is not a reason to name one of them over
         * the others and not a reason to name a candidate that says something short of it.
         *
         * @param names in declaration order
         */
        record AloneSufficient(List<TypeSymbol.AtModule> names) implements Answer {}

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
        record Undifferentiated(List<TypeSymbol.AtModule> names) implements Answer {}
    }

    private final Endpoint end;

    private final List<TypeSymbol.AtModule> candidates;

    private final Ends ends;

    private EndNarrowing(Endpoint end, List<TypeSymbol.AtModule> candidates, Ends ends) {
        this.end = end;
        this.candidates = candidates;
        this.ends = ends;
    }

    /**
     * What the candidates account for at {@code end}, which is nothing unless they moved it there.
     *
     * @param end        where the coordinate stops with every clause read, which is an end that is
     *                   there: a coordinate nothing stops on this side has no end for a declaration
     *                   to have moved anywhere, and a caller with none has its answer already
     * @param candidates the declarations that wrote a relation about it, in the order they were
     *                   found
     * @param ends       the same coordinate read again with clauses taken away
     */
    static Answer read(Endpoint end, List<TypeSymbol.AtModule> candidates, Ends ends) {
        return end.sameAs(ends.without(Set.copyOf(candidates)))
                ? new Answer.NoNarrowing()
                : new EndNarrowing(end, candidates, ends).attribute();
    }

    private Answer attribute() {
        List<TypeSymbol.AtModule> indispensable = new ArrayList<>();
        for (TypeSymbol.AtModule each : candidates) {
            if (!end.sameAs(ends.without(Set.of(each)))) {
                indispensable.add(each);
            }
        }
        if (!indispensable.isEmpty()) {
            return new Answer.Indispensable(inDeclarationOrder(indispensable));
        }
        List<TypeSymbol.AtModule> alone = new ArrayList<>();
        for (TypeSymbol.AtModule each : candidates) {
            if (end.sameAs(ends.without(allBut(each)))) {
                alone.add(each);
            }
        }
        if (!alone.isEmpty()) {
            return new Answer.AloneSufficient(inDeclarationOrder(alone));
        }
        return new Answer.Undifferentiated(inDeclarationOrder(candidates));
    }

    private Set<TypeSymbol.AtModule> allBut(TypeSymbol.AtModule kept) {
        Set<TypeSymbol.AtModule> removed = new LinkedHashSet<>(candidates);
        removed.remove(kept);
        return removed;
    }

    /**
     * In one order, whoever found them. Several of these are one answer and the answer is what a
     * line is told apart by, so an order read off the walk that collected them would make two
     * readings of one edge into two lines.
     *
     * <p>The declaration's own order and not its name alone. Two declarations holding one end can be
     * written in two modules — an inner record's clause and an outer record's reaching the same
     * coordinate at the same value — and two modules may each declare a {@code Span}, so a name is
     * not what tells those two apart.
     */
    private static List<TypeSymbol.AtModule> inDeclarationOrder(List<TypeSymbol.AtModule> found) {
        return found.stream().sorted().toList();
    }
}
