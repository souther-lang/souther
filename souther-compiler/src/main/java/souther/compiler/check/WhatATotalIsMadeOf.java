package souther.compiler.check;

import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.semantics.Accumulation;
import souther.compiler.semantics.PieceOfAnElement;
import souther.compiler.types.BinOp;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.BiFunction;
import java.util.function.Function;

/**
 * How the totals a question reaches stand to each other, read off the lists they are totals of.
 *
 * <p>A total is a sum or a product of the elements of a list, and holds the elements and not their
 * order. A library total holds only its answer to the range of its type and not each step on the
 * way, so what a total is of is exact: the number it comes to is the number of the elements and
 * nothing else, and nothing here says whether a run gets as far as answering it.
 *
 * <p>One decomposition and one kind of law. A list is taken apart into the leaves its elements are
 * held in: the two sides of an append, the argument of a call that lists every element once, and
 * what an element-wise operation ({@code map}, {@code filter}) makes of each side, since such an
 * operation commutes with both. A total is then the sum or the product of the totals of its
 * leaves. A leaf that is itself split — a filter and the filter of the denial, a take and the drop
 * — is the total of what it is split from, and a map by a line is a line of the total it maps.
 * Every one of them is stated of terms, so it is the same whether the lists were written with
 * {@code ++}, through a name, or as a call.
 *
 * <p>Nothing is expanded into a form a reader has not been given: the totals of leaves nobody
 * wrote are atoms of their own, with nothing known of them but how they relate.
 */
final class WhatATotalIsMadeOf {

    /** The atom a term is, of the kind of another atom. */
    private final BiFunction<Term, FactSubject, FactSubject> named;
    /** The atom a term is, as a whole number. */
    private final Function<Term, FactSubject> countNamed;
    private final Term.Interner interned;
    private final BoundOperationFacts facts = DefaultBoundOperationFacts.get();

    /** The operation putting the lists of a written list end to end, which an accumulation of
     *  appending does for lists and for strings alike and this reads for lists only. */
    private static final ValueName JOINING_LISTS = ValueName.Stdlib.operation("List", "concat");

    WhatATotalIsMadeOf(Term.Interner interned, BiFunction<Term, FactSubject, FactSubject> named,
                       Function<Term, FactSubject> countNamed) {
        this.interned = interned;
        this.named = named;
        this.countNamed = countNamed;
    }

    /** A call to a sum or a product, over the list it is a total of. */
    private record Total(ValueName operation, Accumulation how, Term list) {}

    /** What a list is made of once it is held whole: one list, and what holds each of its elements
     *  once. */
    private record Split(Term whole, List<Term> parts) {

        /** The same split of what {@code around} makes of {@code whole} and of each part. */
        Split under(Around around, Term.Interner interned) {
            return new Split(around.of(whole, interned),
                    parts.stream().map(part -> around.of(part, interned)).toList());
        }
    }

    /** An element-wise call with the list it is of left open. */
    private record Around(ValueName operation, List<Term> arguments, int source) {

        Term of(Term inner, Term.Interner interned) {
            List<Term> given = new ArrayList<>(arguments);
            given.set(source, inner);
            return interned.called(operation, given);
        }
    }

    /**
     * What holds of the totals among {@code reached}, as relations.
     *
     * <p>Worked out of the atoms a question reaches and filed against none of them, for the reason
     * a count's relations are ({@link Terms#relationsAmongCounts}).
     */
    List<NumericConstraint> among(Collection<FactSubject> reached) {
        List<NumericConstraint> out = new ArrayList<>();
        Set<Term> filed = new HashSet<>();
        Map<Map.Entry<ValueName, Map<Term, Integer>>, FactSubject> over = new HashMap<>();
        for (FactSubject atom : reached) {
            Total total = totalOf(atom.identity());
            if (total == null) {
                continue;
            }
            Map<Term, Integer> leaves = leavesOf(total.list());
            // Two totals of the same elements are one number, whatever the lists were put
            // together as.
            FactSubject same = over.putIfAbsent(Map.entry(total.operation(), leaves), atom);
            if (same != null) {
                out.add(new NumericConstraint(LinearForm.difference(atom, same), Rel.EQ));
            }
            if (!leaves.equals(Map.of(total.list(), 1))) {
                equate(atom, atom, total, leaves, reached, out);
            }
            for (Term leaf : leaves.keySet()) {
                if (filed.add(totalTerm(total, leaf))) {
                    lawsOf(leaf, total, atom, reached, out);
                }
            }
        }
        return out;
    }

    private Total totalOf(Term term) {
        ValueName operation = term.calledOperation();
        Accumulation how = operation == null ? null : facts.accumulation(operation);
        return how == null || how.combine() == Accumulation.Combine.APPEND
                || term.parts().size() != 1 ? null
                : new Total(operation, how, term.parts().getFirst());
    }

    private Term totalTerm(Total of, Term list) {
        return interned.called(of.operation(), List.of(list));
    }

    // ---- the leaves of a list

    private Map<Term, Integer> leavesOf(Term list) {
        Map<Term, Integer> into = new LinkedHashMap<>();
        decompose(list, List.of(), into);
        return into;
    }

    /**
     * Adds to {@code into} the leaves {@code list} holds the elements of, each as often as it holds
     * them, with {@code around} — what is done to each element on the way, outermost first — done
     * to each.
     */
    private void decompose(Term list, List<Around> around, Map<Term, Integer> into) {
        if (list.shape() == Term.Shape.EMPTY_LIST) {
            return;
        }
        ValueName operation = list.calledOperation();
        List<Term> args = list.parts();
        if (operation != null) {
            if (facts.putsListsEndToEnd(operation) && args.size() == 2) {
                decompose(args.get(0), around, into);
                decompose(args.get(1), around, into);
                return;
            }
            int listed = DefaultBoundOperationFacts.positionOfTheArgumentListedOnce(operation);
            if (listed >= 0 && listed < args.size()) {
                decompose(args.get(listed), around, into);
                return;
            }
            BoundOperationFacts.Assembled made = facts.assembles(operation);
            if (made != null) {
                List<Around> deeper = new ArrayList<>(around);
                deeper.add(new Around(operation, args, made.source().position()));
                decompose(args.get(made.source().position()), deeper, into);
                return;
            }
            if (operation.equals(JOINING_LISTS) && args.getFirst().shape() == Term.Shape.LIST) {
                args.getFirst().parts().forEach(each -> decompose(each, around, into));
                return;
            }
        }
        Term leaf = list;
        for (int i = around.size() - 1; i >= 0; i--) {
            leaf = around.get(i).of(leaf, interned);
        }
        into.merge(leaf, 1, Integer::sum);
    }

    // ---- what a total is of what it is made of

    /**
     * Files that {@code whole}, the total over a list, is what the totals over {@code parts} come
     * to together: their sum for a sum, and the product written of them for a product.
     */
    private void equate(FactSubject whole, FactSubject like, Total of, Map<Term, Integer> parts,
                        Collection<FactSubject> reached, List<NumericConstraint> out) {
        LinearForm<FactSubject> together = switch (of.how().combine()) {
            case ADD -> sumOf(of, parts, like);
            case MULTIPLY -> productOf(of, parts, like, reached);
            case APPEND -> null;
        };
        LinearForm<FactSubject> gap = together == null ? null
                : LinearForm.atom(whole).minus(together).orNull();
        if (gap != null) {
            out.add(new NumericConstraint(gap, Rel.EQ));
        }
    }

    private LinearForm<FactSubject> sumOf(Total of, Map<Term, Integer> parts, FactSubject like) {
        LinearForm<FactSubject> sum = LinearForm.constant(ExactRatio.ZERO);
        for (Map.Entry<Term, Integer> part : parts.entrySet()) {
            FactSubject total = named.apply(totalTerm(of, part.getKey()), like);
            sum = sum.plus(LinearForm.weighing(total, ExactRatio.of(part.getValue()))).orNull();
            if (sum == null) {
                return null;
            }
        }
        return sum;
    }

    /**
     * The product among {@code reached} of totals that hold the elements {@code parts} hold, or
     * null where nothing written is one. A product is not a line in its factors, so it is found as
     * the atom a multiplication of them is, in whatever order and grouping it was written.
     */
    private LinearForm<FactSubject> productOf(Total of, Map<Term, Integer> parts, FactSubject like,
                                              Collection<FactSubject> reached) {
        Map<Term, Integer> wanted = new LinkedHashMap<>();
        parts.forEach((part, times) -> leavesOf(part).forEach(
                (leaf, each) -> wanted.merge(leaf, each * times, Integer::sum)));
        if (wanted.size() == 1 && wanted.containsValue(1)) {
            return LinearForm.atom(named.apply(totalTerm(of, wanted.keySet().iterator().next()), like));
        }
        for (FactSubject written : reached) {
            Map<Term, Integer> held = new LinkedHashMap<>();
            if (written.identity().shape() == Term.Shape.OP
                    && written.identity().carried() == BinOp.MUL
                    && multiplied(written.identity(), of.operation(), held)
                    && held.equals(wanted)) {
                return LinearForm.atom(written);
            }
        }
        return null;
    }

    /** Whether {@code term} is a multiplication of totals by {@code operation}, adding to
     *  {@code into} the leaves of all of them. */
    private boolean multiplied(Term term, ValueName operation, Map<Term, Integer> into) {
        if (term.shape() == Term.Shape.OP && term.carried() == BinOp.MUL) {
            return multiplied(term.parts().get(0), operation, into)
                    && multiplied(term.parts().get(1), operation, into);
        }
        Total factor = totalOf(term);
        if (factor == null || !factor.operation().equals(operation)) {
            return false;
        }
        leavesOf(factor.list()).forEach((leaf, each) -> into.merge(leaf, each, Integer::sum));
        return true;
    }

    // ---- what a leaf is of what it is made from

    private void lawsOf(Term leaf, Total of, FactSubject like, Collection<FactSubject> reached,
                        List<NumericConstraint> out) {
        Split split = splitOf(leaf);
        if (split != null) {
            Map<Term, Integer> parts = new LinkedHashMap<>();
            split.parts().forEach(part -> parts.merge(part, 1, Integer::sum));
            equate(named.apply(totalTerm(of, split.whole()), like), like, of, parts, reached, out);
        }
        if (of.how().combine() == Accumulation.Combine.ADD) {
            scaledBy(leaf, of, like, out);
        }
    }

    /**
     * What {@code list} is split from into what holds each of its elements once: a filter and the
     * filter of the denial of its closure, a take and the drop of the same count. An element-wise
     * call over either is split as what it is over is.
     */
    private Split splitOf(Term list) {
        ValueName operation = list.calledOperation();
        if (operation == null) {
            return null;
        }
        List<Term> args = list.parts();
        BoundOperationFacts.Assembled made = facts.assembles(operation);
        if (made != null) {
            int source = made.source().position();
            Split below = splitOf(args.get(source));
            if (below != null) {
                return below.under(new Around(operation, args, source), interned);
            }
            if (made.piece() != PieceOfAnElement.THE_ELEMENT_WHERE_IT_HOLDS) {
                return null;
            }
            int closure = made.closure().position();
            Term denial = interned.closureDenying(args.get(closure));
            if (denial == null) {
                return null;
            }
            List<Term> denied = new ArrayList<>(args);
            denied.set(closure, denial);
            return new Split(args.get(source), List.of(list, interned.called(operation, denied)));
        }
        BoundOperationFacts.KeptByIndex kept = facts.holdsTheElementsByIndex(operation);
        ValueName other = kept == null ? null : facts.holdingTheOtherSideOfTheIndex(operation);
        return other == null ? null : new Split(args.get(kept.list().position()),
                List.of(list, interned.called(other, args)));
    }

    /**
     * Files that the sum of {@code leaf}, a mapping of a list by a line of the element, is that
     * line of the sum of the list and as many of its constant as the list holds elements.
     */
    private void scaledBy(Term leaf, Total of, FactSubject like, List<NumericConstraint> out) {
        ValueName operation = leaf.calledOperation();
        BoundOperationFacts.Assembled made = operation == null ? null : facts.assembles(operation);
        if (made == null || made.piece() != PieceOfAnElement.THE_CLOSURES_ANSWER) {
            return;
        }
        Term inner = leaf.parts().get(made.source().position());
        LinearForm<List<String>> line =
                leaf.parts().get(made.closure().position()).formAClosureOfOneAnswers();
        // A form of the element itself: no field of it is read.
        if (line == null || !Set.of(List.of()).containsAll(line.coefs().keySet())) {
            return;
        }
        ExactRatio slope = line.coefs().getOrDefault(List.of(), ExactRatio.ZERO);
        LinearForm<FactSubject> mapped = LinearForm.constant(ExactRatio.ZERO);
        if (!slope.isZero()) {
            mapped = LinearForm.weighing(named.apply(totalTerm(of, inner), like), slope);
        }
        if (!line.constant().isZero()) {
            FactSubject howMany = countNamed.apply(
                    interned.called(NumericMeasures.HOW_MANY_A_LIST_HOLDS, List.of(inner)));
            out.add(new NumericConstraint(LinearForm.atom(howMany), Rel.GE));
            mapped = mapped.plus(LinearForm.weighing(howMany, line.constant())).orNull();
        }
        LinearForm<FactSubject> gap = mapped == null ? null
                : LinearForm.atom(named.apply(totalTerm(of, leaf), like)).minus(mapped).orNull();
        if (gap != null) {
            out.add(new NumericConstraint(gap, Rel.EQ));
        }
    }
}
