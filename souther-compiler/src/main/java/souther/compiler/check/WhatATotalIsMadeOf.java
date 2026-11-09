package souther.compiler.check;

import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.semantics.Accumulation;
import souther.compiler.semantics.PieceOfAnElement;
import souther.compiler.types.BinOp;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.BiFunction;
import java.util.function.Function;

/**
 * How the totals a question reaches stand to each other, read off the lists they are totals of.
 *
 * <p>A total is a sum or a product of the elements of a list, and holds the elements and not their
 * order. A library total holds only its answer to the range of its type and not each step on the
 * way, so what it comes to is the exact number of the elements, and a call answers that number
 * wherever it answers at all.
 *
 * <p>Two things are therefore told apart. The call {@code List.sum(xs)} is a number of the type of
 * its elements, and is related to nothing but the exact total of {@code xs}
 * ({@link Term.Shape#EXACT_TOTAL}), which is no number of that type where the elements add up to
 * more than it holds. Every law below is stated of exact totals, so it holds whether or not any
 * list's own call answers; a call is tied to its list's exact total and carries the range its
 * type has.
 *
 * <p>One decomposition and one kind of law. A list is taken apart into the leaves its elements are
 * held in: the two sides of an append, the argument of a call that lists every element once, and
 * what an element-wise operation ({@code map}, {@code filter}) makes of each side, since such an
 * operation commutes with both. An exact total is the sum or the product of the exact totals of
 * its leaves. A leaf that is itself split — a filter and the filter of the denial, a take and the
 * drop — is the exact total of what it is split from, and a map by a line is a line of the exact
 * total it maps. Every one of them is stated of terms, so it is the same whether the lists were
 * written with {@code ++}, through a name, or as a call.
 *
 * <p>Nothing is expanded into a form a reader has not been given: the exact totals of leaves
 * nobody wrote are atoms of their own, with nothing known of them but how they relate.
 */
final class WhatATotalIsMadeOf {

    /** The atom a term is, of the kind of another atom. */
    private final BiFunction<Term, FactSubject, FactSubject> named;
    /** The atom a term is, as a whole number. */
    private final Function<Term, FactSubject> countNamed;
    private final Term.Interner interned;
    private final BoundOperationFacts facts = DefaultBoundOperationFacts.get();

    /**
     * What each list holds the elements of, as the leaves and how often each: a function of the
     * term, so held once for every term met. Empty where the list holds some leaf more often than
     * a count can say, which is no answer and is never read as one.
     */
    private final Map<Term, Optional<Map<Term, Long>>> leaves = new HashMap<>();

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
        Map<Map.Entry<ValueName, Map<Term, Long>>, FactSubject> over = new HashMap<>();
        Written written = multiplicationsAmong(reached);
        for (FactSubject call : reached) {
            Total total = totalOf(call.identity());
            Map<Term, Long> held = total == null ? null : leavesOf(total.list());
            if (held == null) {
                continue;
            }
            FactSubject exact = exactTotal(total, total.list(), call);
            out.add(new NumericConstraint(LinearForm.difference(call, exact), Rel.EQ));
            // Two totals of the same elements are one number, whatever the lists were put
            // together as.
            FactSubject same = over.putIfAbsent(Map.entry(total.operation(), held), exact);
            if (same != null) {
                out.add(new NumericConstraint(LinearForm.difference(exact, same), Rel.EQ));
            }
            if (!held.equals(Map.of(total.list(), 1L))) {
                equate(exact, call, total, held, written, out);
            }
            // What a law is stated of is a list too, and has laws of its own: the list a filter is
            // split from is itself a total, and what is mapped by a line is a list of its own.
            Deque<Term> pending = new ArrayDeque<>(held.keySet());
            while (!pending.isEmpty()) {
                Term list = pending.poll();
                if (filed.add(exactTotal(total, list, call).identity())) {
                    lawsOf(list, total, call, written, out, pending);
                }
            }
        }
        return out;
    }

    /** Whether {@code operation} puts what its container holds end to end, as the library declares
     *  it. Asked of a call that answers a list, it is the one that joins lists. */
    private boolean joinsWhatItHolds(ValueName operation) {
        Accumulation how = facts.accumulation(operation);
        return how != null && how.combine() == Accumulation.Combine.APPEND;
    }

    private Total totalOf(Term term) {
        ValueName operation = term.calledOperation();
        Accumulation how = operation == null ? null : facts.accumulation(operation);
        return how == null || how.combine() == Accumulation.Combine.APPEND
                || term.parts().size() != 1 ? null
                : new Total(operation, how, term.parts().getFirst());
    }

    /** The exact total of {@code list}, of the kind of {@code like}. */
    private FactSubject exactTotal(Total of, Term list, FactSubject like) {
        return named.apply(interned.exactTotal(of.operation(), list), like);
    }

    // ---- the leaves of a list

    /** What {@code list} holds the elements of, or null where that is no count. */
    private Map<Term, Long> leavesOf(Term list) {
        Optional<Map<Term, Long>> known = leaves.get(list);
        if (known == null) {
            known = Optional.ofNullable(decomposed(list));
            leaves.put(list, known);
        }
        return known.orElse(null);
    }

    /**
     * The leaves of {@code list}, each as often as {@code list} holds it: a leaf's own are the
     * leaf, the two sides of an append hold theirs together, a call listing every element once
     * holds what its argument does, and what an element-wise call makes of a list is that call
     * made of each leaf of it.
     */
    private Map<Term, Long> decomposed(Term list) {
        if (list.shape() == Term.Shape.EMPTY_LIST) {
            return Map.of();
        }
        ValueName operation = list.calledOperation();
        List<Term> args = list.parts();
        if (operation == null) {
            return Map.of(list, 1L);
        }
        if (facts.putsListsEndToEnd(operation) && args.size() == 2) {
            return together(args);
        }
        int listed = DefaultBoundOperationFacts.positionOfTheArgumentListedOnce(operation);
        if (listed >= 0 && listed < args.size()) {
            return leavesOf(args.get(listed));
        }
        BoundOperationFacts.Assembled made = facts.assembles(operation);
        if (made != null) {
            Around around = new Around(operation, args, made.source().position());
            Map<Term, Long> inner = leavesOf(args.get(around.source()));
            if (inner == null) {
                return null;
            }
            Map<Term, Long> out = new LinkedHashMap<>();
            inner.forEach((leaf, times) -> out.put(around.of(leaf, interned), times));
            return out;
        }
        if (joinsWhatItHolds(operation) && args.size() == 1
                && args.getFirst().shape() == Term.Shape.LIST) {
            return together(args.getFirst().parts());
        }
        return Map.of(list, 1L);
    }

    /** What the leaves of all of {@code lists} come to together, or null where one of them has no
     *  count or a leaf is held more often than a count can say. */
    private Map<Term, Long> together(List<Term> lists) {
        Map<Term, Long> out = new LinkedHashMap<>();
        for (Term each : lists) {
            Map<Term, Long> some = leavesOf(each);
            if (some == null) {
                return null;
            }
            for (Map.Entry<Term, Long> leaf : some.entrySet()) {
                if (!addTo(out, leaf.getKey(), leaf.getValue())) {
                    return null;
                }
            }
        }
        return out;
    }

    /** Adds {@code times} to what {@code into} holds of {@code leaf}, and answers whether the
     *  count is one a long holds, which is no change where it is not. */
    private static boolean addTo(Map<Term, Long> into, Term leaf, long times) {
        long had = into.getOrDefault(leaf, 0L);
        if (times > Long.MAX_VALUE - had) {
            return false;
        }
        into.put(leaf, had + times);
        return true;
    }

    // ---- what an exact total is of what it is made of

    /**
     * Files that {@code whole}, the exact total over a list, is what the totals over {@code parts}
     * come to together: their sum for a sum, and the product written of them for a product.
     */
    private void equate(FactSubject whole, FactSubject like, Total of, Map<Term, Long> parts,
                        Written written, List<NumericConstraint> out) {
        LinearForm<FactSubject> together = switch (of.how().combine()) {
            case ADD -> sumOf(of, parts, like);
            case MULTIPLY -> productOf(of, parts, like, written);
            case APPEND -> null;
        };
        LinearForm<FactSubject> gap = together == null ? null
                : LinearForm.atom(whole).minus(together).orNull();
        if (gap != null) {
            out.add(new NumericConstraint(gap, Rel.EQ));
        }
    }

    private LinearForm<FactSubject> sumOf(Total of, Map<Term, Long> parts, FactSubject like) {
        LinearForm<FactSubject> sum = LinearForm.constant(ExactRatio.ZERO);
        for (Map.Entry<Term, Long> part : parts.entrySet()) {
            FactSubject exact = exactTotal(of, part.getKey(), like);
            sum = sum.plus(LinearForm.weighing(exact, ExactRatio.of(part.getValue()))).orNull();
            if (sum == null) {
                return null;
            }
        }
        return sum;
    }

    /**
     * The product among those written of totals that hold the elements {@code parts} hold, or null
     * where nothing written is one. A product is not a line in its factors, so it is found as the
     * atom a multiplication of them is, in whatever order and grouping it was written.
     */
    private LinearForm<FactSubject> productOf(Total of, Map<Term, Long> parts, FactSubject like,
                                              Written written) {
        Map<Term, Long> wanted = new LinkedHashMap<>();
        for (Map.Entry<Term, Long> part : parts.entrySet()) {
            Map<Term, Long> some = leavesOf(part.getKey());
            if (some == null) {
                return null;
            }
            for (Map.Entry<Term, Long> leaf : some.entrySet()) {
                long each = leaf.getValue();
                long times = part.getValue();
                if (each > Long.MAX_VALUE / times || !addTo(wanted, leaf.getKey(), each * times)) {
                    return null;
                }
            }
        }
        if (wanted.size() == 1 && wanted.containsValue(1L)) {
            return LinearForm.atom(exactTotal(of, wanted.keySet().iterator().next(), like));
        }
        FactSubject product = written.byWhatItMultiplies().get(Map.entry(of.operation(), wanted));
        return product == null ? null : LinearForm.atom(product);
    }

    /** The multiplications of totals among the atoms a question reaches, by what the totals
     *  multiplied hold the elements of between them. */
    private record Written(Map<Map.Entry<ValueName, Map<Term, Long>>, FactSubject> byWhatItMultiplies) {}

    /** What a multiplication of totals by one operation holds the elements of between its
     *  factors. */
    private record Multiplied(ValueName operation, Map<Term, Long> leaves) {}

    /** What each term that is a multiplication of totals holds the elements of, once for each
     *  term: empty where it is no such multiplication or holds some leaf more often than a count
     *  says. */
    private final Map<Term, Optional<Multiplied>> multiplications = new HashMap<>();

    private Written multiplicationsAmong(Collection<FactSubject> reached) {
        Map<Map.Entry<ValueName, Map<Term, Long>>, FactSubject> out = new HashMap<>();
        for (FactSubject atom : reached) {
            Term term = atom.identity();
            Multiplied held = term.shape() == Term.Shape.OP && term.carried() == BinOp.MUL
                    ? multipliedBy(term).orElse(null) : null;
            if (held != null) {
                out.putIfAbsent(Map.entry(held.operation(), held.leaves()), atom);
            }
        }
        return new Written(out);
    }

    /** What {@code term}, a product of factors, holds the elements of: each factor a total by
     *  the one operation, and the multiplications among them however they are grouped. */
    private Optional<Multiplied> multipliedBy(Term term) {
        Optional<Multiplied> known = multiplications.get(term);
        if (known == null) {
            known = Optional.ofNullable(multipliedOf(term));
            multiplications.put(term, known);
        }
        return known;
    }

    private Multiplied multipliedOf(Term term) {
        List<Term> factors = term.shape() == Term.Shape.OP && term.carried() == BinOp.MUL
                ? term.parts() : List.of();
        if (factors.isEmpty()) {
            Total total = totalOf(term);
            Map<Term, Long> some = total == null ? null : leavesOf(total.list());
            return some == null ? null : new Multiplied(total.operation(), some);
        }
        Multiplied left = multipliedBy(factors.get(0)).orElse(null);
        Multiplied right = multipliedBy(factors.get(1)).orElse(null);
        if (left == null || right == null || !left.operation().equals(right.operation())) {
            return null;
        }
        Map<Term, Long> leaves = new LinkedHashMap<>(left.leaves());
        for (Map.Entry<Term, Long> leaf : right.leaves().entrySet()) {
            if (!addTo(leaves, leaf.getKey(), leaf.getValue())) {
                return null;
            }
        }
        return new Multiplied(left.operation(), leaves);
    }

    // ---- what a leaf is of what it is made from

    /** Files the laws of {@code list}, and adds to {@code pending} the lists they are stated of. */
    private void lawsOf(Term list, Total of, FactSubject like, Written written,
                        List<NumericConstraint> out, Collection<Term> pending) {
        Split split = splitOf(list);
        if (split != null) {
            Map<Term, Long> parts = new LinkedHashMap<>();
            split.parts().forEach(part -> parts.merge(part, 1L, Long::sum));
            equate(exactTotal(of, split.whole(), like), like, of, parts, written, out);
            pending.add(split.whole());
            pending.addAll(split.parts());
        }
        if (of.how().combine() == Accumulation.Combine.ADD) {
            Term inner = scaledBy(list, of, like, out);
            if (inner != null) {
                pending.add(inner);
            }
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
     * Files that the exact sum of {@code leaf}, a mapping of a list by a line of the element, is
     * that line of the exact sum of the list and as many of its constant as the list holds
     * elements. Answers the list it maps, or null where {@code leaf} is no such mapping.
     */
    private Term scaledBy(Term leaf, Total of, FactSubject like, List<NumericConstraint> out) {
        ValueName operation = leaf.calledOperation();
        BoundOperationFacts.Assembled made = operation == null ? null : facts.assembles(operation);
        if (made == null || made.piece() != PieceOfAnElement.THE_CLOSURES_ANSWER) {
            return null;
        }
        Term inner = leaf.parts().get(made.source().position());
        LinearForm<List<String>> line =
                leaf.parts().get(made.closure().position()).formAClosureOfOneAnswers();
        // A form of the element itself: no field of it is read.
        if (line == null || !Set.of(List.of()).containsAll(line.coefs().keySet())) {
            return null;
        }
        ExactRatio slope = line.coefs().getOrDefault(List.of(), ExactRatio.ZERO);
        LinearForm<FactSubject> mapped = LinearForm.constant(ExactRatio.ZERO);
        if (!slope.isZero()) {
            mapped = LinearForm.weighing(exactTotal(of, inner, like), slope);
        }
        if (!line.constant().isZero()) {
            ValueName count = facts.countOf(Type.EMPTY_LIST);
            if (count == null) {
                return null;
            }
            FactSubject howMany = countNamed.apply(interned.called(count, List.of(inner)));
            out.add(new NumericConstraint(LinearForm.atom(howMany), Rel.GE));
            mapped = mapped.plus(LinearForm.weighing(howMany, line.constant())).orNull();
        }
        LinearForm<FactSubject> gap = mapped == null ? null
                : LinearForm.atom(exactTotal(of, leaf, like)).minus(mapped).orNull();
        if (gap != null) {
            out.add(new NumericConstraint(gap, Rel.EQ));
        }
        return inner;
    }
}
