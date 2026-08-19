package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.core.Core;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.NumericDomain.Bounds;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;

import java.math.BigDecimal;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

/**
 * What holds of everything a reduction's step is handed besides its accumulator, whatever the
 * container holds and however far the walk has got.
 *
 * <p>Plural, and rooted. A step is handed the accumulator and everything else the operation applies
 * it to, and that is not one value: {@code Map.fold} hands its step a key and a value, and the two
 * are bounded by different declarations. So this is facts about places, each rooted at the parameter
 * it arrives on, rather than a range for "the element". Today only the parameter
 * {@link Combinators} names the element on is populated — a key is a place nothing here reads yet —
 * and widening that changes what is put in this, not the shape of it or of anything downstream.
 *
 * <p>Bounds and not relations, for now. Two places under one parameter may stand in a relation the
 * declaration states — {@code end >= start} — and nothing here carries it. That is a narrowing of
 * what can be proved and is written down as one: a reduction whose step needs such a relation gets
 * no bound rather than a wrong one.
 *
 * <p>What is here holds of <em>every</em> value the step is handed, so it may be assumed of the one
 * value the step is read against. Nothing that holds of some elements belongs here: a guard about
 * one element of a list says nothing about the element the walk is at, and putting it here would
 * make the induction prove something no walk establishes.
 */
record StepInputFacts(Map<FactSubject, Bounds> at, Map<FactSubject, Granularity> kinds) {

    StepInputFacts {
        at = Map.copyOf(at);
        kinds = Map.copyOf(kinds);
    }

    static StepInputFacts none() {
        return new StepInputFacts(Map.of(), Map.of());
    }

    /**
     * What holds of everything {@code r}'s step is handed besides its accumulator.
     *
     * <p>Two sources, and they are two different kinds of fact. What a value's type declares holds of
     * every value of that type, so it holds of whichever one the walk is at. What a container written
     * out holds is read off the line it is written on: three elements written there are the only
     * three there are, and every one of them lies between the least and the greatest.
     *
     * <p>Read at every step of a chain rather than at the end of it. A newtype's {@code .value} is
     * the same value as the newtype, so {@code x.amount.value} is the place {@code x.amount} is —
     * and the rules that bound it are written on {@code x.amount}'s type, not on the {@code Int} the
     * read answers. Asking at each level is what puts the rule and the place together without this
     * having a second opinion about which reads are steps.
     */
    static StepInputFacts of(Reductions.Reducing r, Denotations inside, Terms terms,
                             Symbols symbols) {
        Set<BindingId> handed = new HashSet<>();
        for (Hir.Binder param : r.step().params()) {
            if (param != r.accumulator()) {
                handed.add(param.id());
            }
        }
        Gathering gathering = new Gathering();
        declaring(r.step().body(), handed, inside, terms, symbols, gathering);
        writtenOut(r, inside, terms, gathering);
        return gathering.gathered();
    }

    /** Every place the step reads off something it was handed, bounded by what its type declares. */
    private static void declaring(Core e, Set<BindingId> handed, Denotations inside, Terms terms,
                                  Symbols symbols, Gathering gathering) {
        BindingId root = Terms.rootBinding(e);
        if (root != null && handed.contains(root)) {
            FactSubject atom = terms.positionOf(e, inside).atom();
            if (atom != null) {
                gathering.holds(atom, declared(e.type(), symbols), terms.granularityOf(e.type()));
            }
        }
        Core.forEachChild(e, child -> declaring(child, handed, inside, terms, symbols, gathering));
    }

    /** What {@code type}'s own rules leave a value of it between, as the domain reads a range. */
    private static Bounds declared(Type type, Symbols symbols) {
        DeclaredBounds.Bounds own = DeclaredBounds.of(type, symbols);
        if (own == null || own.isEmpty()) {
            return null;
        }
        return new Bounds(own.min() == null ? null : own.min().at(),
                own.max() == null ? null : own.max().at());
    }

    /**
     * The element of a container written out, bounded by the elements written there.
     *
     * <p>Only where every one of them is a number this folds. A container written with a computed
     * element says nothing here — the least of what is written is not the least of what is held once
     * one of them is decided at run time — and saying nothing is what leaves the walk unbounded
     * rather than wrongly bounded.
     */
    private static void writtenOut(Reductions.Reducing r, Denotations inside, Terms terms,
                                   Gathering gathering) {
        Type element = Terms.elementType(r.container().type());
        if (element == null || !(terms.listedOut(r.container(), inside) instanceof Core.ListLit list)
                || list.elements().isEmpty()) {
            return;
        }
        BigDecimal low = null;
        BigDecimal high = null;
        for (Core each : list.elements()) {
            BigDecimal written = Terms.constantNumber(each);
            if (written == null) {
                return;
            }
            low = low == null || written.compareTo(low) < 0 ? written : low;
            high = high == null || written.compareTo(high) > 0 ? written : high;
        }
        FactSubject atom = terms.positionOf(
                Terms.read(r.element(), element, r.step().pos()), inside).atom();
        if (atom == null) {
            return;
        }
        gathering.holds(atom,
                new Bounds(Endpoint.inclusive(Count.of(low)), Endpoint.inclusive(Count.of(high))),
                terms.granularityOf(element));
    }

    /** {@code domain} with all of this taken as holding. Handed a domain rather than answering with
     * one, because which domain these are assumed into is the caller's question: they hold of every
     * element and so hold under any reading, and the reading is what decides what else is true
     * beside them. */
    NumericDomain<FactSubject> taking(NumericDomain<FactSubject> domain) {
        NumericDomain<FactSubject> out = domain;
        for (Map.Entry<FactSubject, Bounds> one : at.entrySet()) {
            out = out.assuming(one.getKey(), one.getValue(), kinds);
        }
        return out;
    }

    /** A builder that keeps the two tables in step, since a bound recorded without how its atom's
     * values are spaced is one the domain refuses to take. */
    static final class Gathering {

        private final Map<FactSubject, Bounds> at = new LinkedHashMap<>();
        private final Map<FactSubject, Granularity> kinds = new LinkedHashMap<>();

        /**
         * Records that {@code atom} lies between {@code bounds}, where that says anything.
         *
         * <p>Two rules reaching one atom both hold of it, so the tighter end of each side is kept.
         * One place can be read at more than one level of a chain and be bounded at more than one:
         * a newtype's rule and the rule on what it wraps are two rules about one value.
         */
        void holds(FactSubject atom, Bounds bounds, Granularity spacing) {
            if (bounds == null || bounds.isEmpty()) {
                return;
            }
            Bounds had = at.get(atom);
            at.put(atom, had == null ? bounds
                    : new Bounds(Endpoint.lower(had.min(), bounds.min()),
                            Endpoint.upper(had.max(), bounds.max())));
            kinds.put(atom, spacing);
        }

        StepInputFacts gathered() {
            return at.isEmpty() ? none() : new StepInputFacts(at, kinds);
        }
    }
}
