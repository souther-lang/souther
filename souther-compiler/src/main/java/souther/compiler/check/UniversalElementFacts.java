package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.core.Core;
import souther.compiler.types.BindingId;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain.Bounds;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.math.BigDecimal;
import java.util.LinkedHashMap;
import java.util.Map;

/**
 * What holds of every element a container expression holds, wherever the container came from.
 *
 * <p>Read off the tree the discharge check is given, which is one where the library's own operations
 * are still calls ({@code InliningPolicy#DISCHARGE}). So this is not a record of what some earlier
 * pass observed: it is the same question asked again of the expression a container is written as —
 * what its own type and its own written-out elements say, and what a construction keeps of the
 * container it was built from.
 *
 * <p>Keyed by the path under an element and not by a subject. What holds of an element is a fact
 * about {@code amount} of every element, or about the element itself ({@code ""}); which value the
 * reader is standing at, and what that value is called there, is the reader's own question. That is
 * what lets a producer and a consumer that share no binder share a fact: {@code List.map(x -> x.value,
 * xs)} says of the list it answers that every element of it is at or above nought, and the fold or
 * the accumulation that walks that list never met {@code x}.
 *
 * <p>Everything here holds of <em>every</em> element, so a reader may assume it of the one element
 * it is standing at. Nothing that holds of some elements belongs here, and nothing about how many
 * elements there are: that a container written out with nothing in it makes a walk answer its seed
 * is true and is not this — it is a fact about the count, and stating it here would make a reader
 * that assumes these of an element assume something no element satisfies.
 */
record UniversalElementFacts(Map<String, Bounds> byPath) {

    UniversalElementFacts {
        byPath = Map.copyOf(byPath);
    }

    private static final UniversalElementFacts NONE = new UniversalElementFacts(Map.of());

    static UniversalElementFacts none() {
        return NONE;
    }

    boolean saysNothing() {
        return byPath.isEmpty();
    }

    /**
     * What holds of every element of {@code container}.
     *
     * <p>Two sources and one transfer. A value's type guarantees what it guarantees of every value
     * of it, so the container's element type says it of every element; a container written out holds
     * the elements written there and nothing else, so every one of them lies between the least and
     * the greatest. Beside those, what a construction was built from says what it kept
     * ({@link #transferred}).
     */
    static UniversalElementFacts of(Core container, Denotations at, Terms terms, Symbols symbols,
                                    ReadingPolicy policy) {
        if (container == null) {
            return NONE;
        }
        Map<String, Bounds> held = new LinkedHashMap<>();
        Type element = Terms.elementType(container.type());
        guaranteed(element, symbols, policy).forEach((path, bounds) -> holds(held, path, bounds));
        writtenOut(container, element, at, terms, held);
        transferred(container, at, terms, symbols, policy, held);
        return held.isEmpty() ? NONE : new UniversalElementFacts(held);
    }

    /**
     * These of the value at {@code root}, as the subjects a reader files facts under.
     *
     * <p>The instantiation, and the only place a path becomes a subject. A reader hands the place it
     * is standing at and gets back what holds there — which is what keeps the facts themselves free
     * of whatever binder either side happened to be written with.
     */
    Map<FactSubject, Bounds> at(FactSubject root, Terms terms) {
        Map<FactSubject, Bounds> instantiated = new LinkedHashMap<>();
        byPath.forEach((path, bounds) -> {
            FactSubject subject = terms.under(root, path);
            if (subject != null) {
                instantiated.put(subject, bounds);
            }
        });
        return instantiated;
    }

    /**
     * What a value of {@code type} guarantees, by the path under it each bound is about.
     *
     * <p>{@link InvariantChecker#seedFields} is what decides it and this reads that answer: a
     * record's own invariant bounds its fields, and a reading of the declarations is what has that.
     * Shared with {@link StepInputFacts}, which asks it of a parameter that is not an element — a
     * key a {@code Map.fold} hands its step is bounded by its own declaration and by nothing about
     * the container's elements.
     */
    static Map<String, Bounds> guaranteed(Type type, Symbols symbols, ReadingPolicy policy) {
        if (!(type instanceof Type.Ref ref)
                || !(symbols.declarations().declaration(ref.name().key()) instanceof Hir.Data data)) {
            return Map.of();
        }
        InvariantChecker.Seeded seeded = seededOf(ref.name(), data, symbols, policy);
        if (seeded == null) {
            return Map.of();
        }
        Map<String, Bounds> guaranteed = new LinkedHashMap<>();
        seeded.atoms().forEach((path, atom) -> {
            Bounds bounds = seeded.numbers().boundsOf(atom);
            if (bounds != null && !bounds.saysNothing()) {
                guaranteed.put(path, bounds);
            }
        });
        return guaranteed;
    }

    /** The reading of {@code named}, or null where it fell over. A reading that fell over is one
     * this says nothing from, which leaves an element unbounded rather than bounded by half of what
     * a declaration says. */
    private static InvariantChecker.Seeded seededOf(TypeSymbol named, Hir.Data data,
                                                    Symbols symbols, ReadingPolicy policy) {
        InvariantChecker.Seeded seeded = InvariantChecker.seedFields(named, data, symbols, policy);
        return seeded.everyClauseRead() && !seeded.constraints().isBottom() ? seeded : null;
    }

    /**
     * The elements of a container written out, bounded by the elements written there.
     *
     * <p>Only where every one of them is a number this folds. A container written with a computed
     * element says nothing here — the least of what is written is not the least of what is held once
     * one of them is decided at run time — and saying nothing is what leaves a reader unbounded
     * rather than wrongly bounded.
     */
    private static void writtenOut(Core container, Type element, Denotations at, Terms terms,
                                   Map<String, Bounds> held) {
        if (element == null
                || !(terms.listedOut(container, at) instanceof Core.ListLit list)
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
        holds(held, FieldDomains.THE_VALUE,
                new Bounds(Endpoint.inclusive(Count.of(low)), Endpoint.inclusive(Count.of(high))));
    }

    /**
     * What a construction kept of the container it was built from.
     *
     * <p>Four words and an answer for each of them ({@link DischargeRules.Shape}), because a word
     * that fell through to the answer beside it is how a reading comes to say of an element
     * something no element satisfies. The same elements in another order, or some of them, are
     * elements a property of every element was already true of. A new element for each is the
     * closure's answer, so what holds of it is read through the closure and not from the source.
     *
     * <p>{@code COLLAPSES} says nothing, and that is written down rather than left out. At most one
     * new element for each is what {@code List.filterMap} answers, where an element is what a
     * closure's answer held rather than the answer itself — so the projection the mapped case makes
     * is not the one to make here, and until a reading of that is written the honest answer is that
     * this keeps nothing.
     */
    private static void transferred(Core container, Denotations at, Terms terms, Symbols symbols,
                                    ReadingPolicy policy, Map<String, Bounds> held) {
        if (!(container instanceof Core.PreservedCall call)) {
            return;
        }
        DischargeRules.Source built = DischargeRules.builtFrom(call);
        if (built == null || built.container() == null) {
            return;
        }
        switch (built.shape()) {
            case PERMUTES, SUBSET ->
                    of(built.container(), at, terms, symbols, policy).byPath()
                            .forEach((path, bounds) -> holds(held, path, bounds));
            case MAPS -> throughTheClosure(call, built.container(), at, terms, symbols, policy, held);
            case COLLAPSES -> { }
        }
    }

    /**
     * What holds of what the closure answered, where what it answers is a place of the element it
     * was handed.
     *
     * <p>A closure that answers a place of its element — {@code x -> x.value}, {@code x -> x.amount}
     * — hands on what was true there: what held of that place of every element of the source holds
     * of every element of the list answered. A closure that computes anything else says nothing
     * here. What it computes is arithmetic, and reading it would be this deciding what an expression
     * is worth, which is a question with an owner ({@link DerivedNumericFacts}) and one that cannot
     * be asked of a closure standing where no accumulator has been assumed.
     *
     * <p>Which place it answered is asked of the subjects and not of the fields written. The two are
     * not the same question: a newtype's carrier is read as {@code x.value} and is the value itself,
     * so the path that names it is the empty one, and a reader that counted the fields it saw would
     * have gone looking for what holds of a place under a number. So the element is entered
     * somewhere nothing else names, the closure's answer is asked which subject it is, and the paths
     * the source states are put under that same root until one of them is that subject — the algebra
     * deciding which two spellings are one place, as it does everywhere else.
     */
    private static void throughTheClosure(Core.PreservedCall call, Core source, Denotations at,
                                          Terms terms, Symbols symbols, ReadingPolicy policy,
                                          Map<String, Bounds> held) {
        Combinators.Handed handed = Combinators.handedTo(call, at);
        if (handed == null) {
            return;
        }
        UniversalElementFacts kept = of(source, at, terms, symbols, policy);
        if (kept.saysNothing()) {
            return;
        }
        BindingId element = handed.element().binding();
        FactSubject root = terms.placeSubject(element);
        Denotations reading = at.location(element, root, terms.placeTerm(element));
        FactSubject answered = terms.subjectOf(handed.step().body(), reading);
        if (answered == null) {
            return;
        }
        kept.byPath().forEach((path, bounds) -> {
            if (answered.equals(terms.under(root, path))) {
                holds(held, FieldDomains.THE_VALUE, bounds);
            }
        });
    }

    /** Records that everything at {@code path} lies between {@code bounds}. Two sources reaching one
     * place are both true of it, so the tighter end of each side is kept. */
    private static void holds(Map<String, Bounds> held, String path, Bounds bounds) {
        if (bounds == null || bounds.saysNothing()) {
            return;
        }
        Bounds had = held.get(path);
        held.put(path, had == null ? bounds : had.meet(bounds));
    }
}
