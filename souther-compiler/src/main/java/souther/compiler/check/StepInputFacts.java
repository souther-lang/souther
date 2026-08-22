package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.core.Core;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.NumericDomain.Bounds;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.math.BigDecimal;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * What holds of everything a reduction's step is handed besides its accumulator, whatever the
 * container holds and however far the walk has got.
 *
 * <p>Plural, and rooted. A step is handed the accumulator and everything else the operation applies
 * it to, and that is not one value: {@code Map.fold} hands its step a key and a value, and the two
 * are bounded by different declarations. So this is facts about places, each rooted at the parameter
 * it arrives on, rather than a range for "the element" — and every parameter but the accumulator is
 * read, so a key is read the day a step is written over one.
 *
 * <p>What a value of a type guarantees is not decided here. {@link InvariantChecker#seedFields} is
 * what decides it, and this projects that answer onto the places the walk names — the same
 * projection {@link FieldDomains} makes of the same reading. Read here instead, only a numeric
 * newtype's own rules would have been found: a record's own invariant bounds its fields, and
 * {@code data Line = { amount: Int } invariant amount >= 0} says nothing about any type
 * {@code DeclaredBounds} would have been asked about. That fact is one the walk into a combinator's
 * closure already has ({@link InvariantChecker#walkCall} enters the element and seeds it), so
 * deciding it a second way here would have been two answers to one question, differing by which of
 * them a reader happened to ask.
 *
 * <p>Bounds and not relations. Two places under one parameter may stand in a relation the
 * declaration states — {@code end >= start} — and the projection drops it, as {@link FieldDomains}'
 * does. That is a narrowing of what can be proved and is written down as one: a reduction whose step
 * needs such a relation gets no bound rather than a wrong one.
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
     * What holds of everything {@code r}'s step is handed besides its accumulator, where each of
     * those parameters is entered in {@code inside} as the place it is.
     *
     * <p>Two sources, and they are two different kinds of fact. What a value's type guarantees holds
     * of every value of that type, so it holds of whichever one the walk is at. What a container
     * written out holds is read off the line it is written on: three elements written there are the
     * only three there are, and every one of them lies between the least and the greatest.
     */
    static StepInputFacts of(Reductions.Reducing r, Denotations inside, Terms terms,
                             Symbols symbols, ReadingPolicy policy,
                             Set<FactSubject> namedByTheStep) {
        Gathering gathering = new Gathering(terms, namedByTheStep);
        List<Core.Binder> params = r.step().params();
        for (int i = 0; i < params.size(); i++) {
            if (params.get(i) == r.accumulator()) {
                continue;
            }
            guaranteed(params.get(i), handedAt(r, i), inside, terms, symbols, policy, gathering);
        }
        writtenOut(r, inside, terms, gathering);
        return gathering.gathered();
    }

    /**
     * What the step's parameter at {@code i} is handed, as a type.
     *
     * <p>The same two answers {@link InvariantChecker#walkCall} enters a closure's parameters at:
     * the element arrives at whatever the container holds, and every other parameter at what the
     * closure was typed with. Read the same way here so that a reduction proves against the types
     * the walk into that closure already reads it against.
     */
    private static Type handedAt(Reductions.Reducing r, int i) {
        if (r.step().params().get(i) == r.element()) {
            return Terms.elementType(r.container().type());
        }
        return r.step().type() instanceof Type.FnOf fn && i < fn.params().size()
                ? fn.params().get(i) : null;
    }

    /**
     * What a value of {@code param}'s type guarantees, projected onto the places under the parameter.
     *
     * <p>{@link InvariantChecker#seedFields} answers by path — {@code ""} for the value itself,
     * {@code "amount"} for a field, {@code "a.b"} for a field of one — and the walk names those same
     * places under whatever subject the parameter was entered as. So the projection is the path read
     * off one and put back on the other, and nothing here reads a declaration.
     */
    private static void guaranteed(Core.Binder param, Type handed, Denotations inside, Terms terms,
                                   Symbols symbols, ReadingPolicy policy, Gathering gathering) {
        FactSubject root = inside.subject(param.binding());
        if (root == null || !(handed instanceof Type.Ref ref)
                || !(symbols.declarations().declaration(ref.name().key()) instanceof Hir.Data data)) {
            return;
        }
        InvariantChecker.Seeded seeded = seededOf(ref.name(), data, symbols, policy);
        if (seeded == null) {
            return;
        }
        seeded.atoms().forEach((path, atom) ->
                gathering.holds(terms.under(root, path), seeded.numbers().boundsOf(atom)));
    }

    /** The reading of {@code named}, or null where it fell over. A reading that fell over is one
     * this says nothing from, which leaves the walk unbounded rather than bounded by half of what a
     * declaration says. */
    private static InvariantChecker.Seeded seededOf(TypeSymbol named, Hir.Data data,
                                                    Symbols symbols, ReadingPolicy policy) {
        InvariantChecker.Seeded seeded = InvariantChecker.seedFields(named, data, symbols, policy);
        return seeded.everyClauseRead() && !seeded.constraints().isBottom() ? seeded : null;
    }

    /**
     * The element of a container written out, bounded by the elements written there.
     *
     * <p>Only where every one of them is a number this folds. A container written with a computed
     * element says nothing here — the least of what is written is not the least of what is held once
     * one of them is decided at run time — and saying nothing is what leaves the walk unbounded
     * rather than wrongly bounded.
     *
     * <p>A container written out with nothing in it says nothing either, and that is a narrowing
     * this does not reach past: what it would establish is that the step never runs, which is a fact
     * about how many elements there are and not about what any of them is.
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
        gathering.holds(
                terms.positionOf(Terms.read(r.element(), element, r.step().pos()), inside).atom(),
                new Bounds(Endpoint.inclusive(Count.of(low)), Endpoint.inclusive(Count.of(high))));
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

    /**
     * A builder that keeps the two tables in step, and that keeps only the places the step names.
     *
     * <p>Both for one reason. A bound recorded without how its atom's values are spaced is one the
     * domain refuses to take, and how they are spaced is what the naming recorded when the step was
     * read — so a place the step does not name has no answer there, and is also a place no bound
     * could be read at. The two questions have one answer and it is asked once.
     */
    static final class Gathering {

        private final Map<FactSubject, Bounds> at = new LinkedHashMap<>();
        private final Map<FactSubject, Granularity> kinds = new LinkedHashMap<>();
        private final Terms terms;
        private final Set<FactSubject> namedByTheStep;

        Gathering(Terms terms, Set<FactSubject> namedByTheStep) {
            this.terms = terms;
            this.namedByTheStep = namedByTheStep;
        }

        /**
         * Records that {@code atom} lies between {@code bounds}, where that says anything and the
         * step names it.
         *
         * <p>Two rules reaching one atom both hold of it, so the tighter end of each side is kept.
         * One place can be reached by more than one source — a type that guarantees a range and a
         * container written out holding narrower values — and both are true of it.
         */
        void holds(FactSubject atom, Bounds bounds) {
            if (atom == null || bounds == null || bounds.saysNothing()
                    || !namedByTheStep.contains(atom)) {
                return;
            }
            Bounds had = at.get(atom);
            at.put(atom, had == null ? bounds : had.meet(bounds));
            kinds.putAll(terms.kindsOf(NumericDomain.LinearForm.atom(atom)));
        }

        StepInputFacts gathered() {
            return at.isEmpty() ? none() : new StepInputFacts(at, kinds);
        }
    }

    /** The fields a path names, from the head down. */
    static List<String> stepsOf(String path) {
        return path.isEmpty() ? List.of() : List.of(path.split("\\."));
    }
}
