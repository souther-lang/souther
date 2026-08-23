package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.core.Core;
import souther.compiler.types.BindingId;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.NumericDomain.Bounds;
import souther.compiler.numeric.NumericDomain.LinearForm;
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
     *
     * <p>The name a container was given is followed once, here, and every reading below is of what
     * it was given. A name is not a third kind of container: {@code List.sum(ys)} where {@code ys}
     * was bound to {@code List.map(f, xs)} is the same question as the one written in a line, and a
     * reading that followed the name for the elements written out and not for what the construction
     * kept would answer the two differently — which is the shape of what this class was written to
     * stop, seen inside it.
     */
    static UniversalElementFacts of(Core written, Denotations at, Terms terms, Symbols symbols,
                                    ReadingPolicy policy) {
        if (written == null) {
            return NONE;
        }
        Core container = terms.listedOut(written, at);
        Map<String, Bounds> held = new LinkedHashMap<>();
        Type element = Terms.elementType(container.type());
        guaranteed(element, symbols, policy).forEach((path, bounds) -> holds(held, path, bounds));
        writtenOut(container, element, held);
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
    private static void writtenOut(Core container, Type element, Map<String, Bounds> held) {
        if (element == null || !(container instanceof Core.ListLit list)
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
     * <p>Read off the lineage and not off the four words it projects to. The words answer whether
     * what was known survives, which is one bit where this has an answer per alternative: what
     * {@code Map.updateIfPresent} answers holds values the closure made and values that were already
     * there, and a reader with one word for the run can only say the true thing about neither.
     *
     * <p>An answer for each of the four lineages, because a case that fell through to the one beside
     * it is how a reading comes to say of an element something no element satisfies. The same
     * elements keep what was true of every one of them, however many of them there are — how many is
     * {@link DischargeRules.Cardinality} and is a different algebra, so {@code Set.map} carries what
     * its closure answered exactly as {@code List.map} does. An element inside what a closure
     * answered is not what the closure answered, and nothing here reads into a list or an optional,
     * so that one keeps nothing. One of several is what holds of every one of them, which is the
     * span of what each keeps.
     */
    private static void transferred(Core container, Denotations at, Terms terms, Symbols symbols,
                                    ReadingPolicy policy, Map<String, Bounds> held) {
        if (!(container instanceof Core.PreservedCall call)) {
            return;
        }
        DischargeRules.Kept kept = DischargeRules.keptFrom(call);
        if (kept == null || kept.container() == null) {
            return;
        }
        keptBy(kept.lineage(), call, kept.container(), at, terms, symbols, policy)
                .forEach((path, bounds) -> holds(held, path, bounds));
    }

    /** What one lineage keeps of {@code source}, by the path under an element. */
    private static Map<String, Bounds> keptBy(ElementLineage lineage, Core.PreservedCall call,
                                              Core source, Denotations at, Terms terms,
                                              Symbols symbols, ReadingPolicy policy) {
        return switch (lineage) {
            case ElementLineage.SameAs _ -> of(source, at, terms, symbols, policy).byPath();
            case ElementLineage.ClosureResult _ ->
                    throughTheClosure(call, source, at, terms, symbols, policy);
            case ElementLineage.InsideClosureResult _ -> Map.of();
            case ElementLineage.OneOf one -> {
                Map<String, Bounds> both = null;
                for (ElementLineage alternative : one.alternatives()) {
                    Map<String, Bounds> keeps =
                            keptBy(alternative, call, source, at, terms, symbols, policy);
                    both = both == null ? keeps : spanning(both, keeps);
                }
                yield both == null ? Map.of() : both;
            }
        };
    }

    /**
     * What holds of an element that is one of two things: what holds of both.
     *
     * <p>A place either of them says nothing about is a place nothing is said about, and the ends
     * are the outer ones of the two — an element the closure never saw is bounded by what the source
     * guarantees, and one it made is bounded by what it answered, and every element is one of the
     * two.
     */
    private static Map<String, Bounds> spanning(Map<String, Bounds> one, Map<String, Bounds> other) {
        Map<String, Bounds> both = new LinkedHashMap<>();
        one.forEach((path, bounds) -> {
            Bounds there = other.get(path);
            if (there != null) {
                both.put(path, Bounds.spanning(bounds, there));
            }
        });
        return both;
    }

    /**
     * What holds of what the closure answered, given what holds of every element it is applied to.
     *
     * <p>Not a projection of the paths. A closure answers a value it computed — {@code x -> 0},
     * {@code x -> x.value + 1}, {@code x -> x.value} — and what holds of that value is what the
     * arithmetic makes of what holds of the element. So the element is entered somewhere nothing
     * else names, what the closure answers is read as a form over that place, and the facts the
     * source states are assumed of it: what the reading proves of the form holds of every element of
     * the list answered, since it was proved of an element nothing but those facts is true of.
     *
     * <p>The reading is the one that reads recipes and what values carry
     * ({@link DerivedNumericFacts#refine}), and not one assembled here. What a form is worth is two
     * stages — everything the atoms it reaches carry, and then what follows about the arithmetic the
     * affine fragment cannot hold — and a caller that asked a raw domain instead would get a second
     * reader that knows neither: {@code x -> x.value * x.value} names an atom whose recipe says it
     * is a product, and {@code x -> Int.abs(x)} names one the library says is never negative. Both
     * are read where a fold's step is read, and a walk over what the closure built would have lost
     * them — the same value readable or not by where the tree put it, which is what this class is
     * for.
     *
     * <p>What is assumed into that reading is what every element satisfies and nothing else. Nothing
     * of where the call stands goes in: a closure is applied to every element, so what is true where
     * one of them was named is not true of what it answers.
     */
    private static Map<String, Bounds> throughTheClosure(Core.PreservedCall call, Core source,
                                                         Denotations at, Terms terms,
                                                         Symbols symbols, ReadingPolicy policy) {
        Combinators.Handed handed = Combinators.handedTo(call, at);
        if (handed == null) {
            return Map.of();
        }
        UniversalElementFacts kept = of(source, at, terms, symbols, policy);
        BindingId element = handed.element().binding();
        FactSubject root = terms.placeSubject(element);
        Denotations reading = at.location(element, root, terms.placeTerm(element));
        // Read before anything is assumed: reading the closure is what names the places inside it,
        // and a place with no name is one no range can be asserted about.
        LinearForm<FactSubject> answered = terms.affineOf(handed.step().body(), reading);
        if (answered == null) {
            return Map.of();
        }
        NumericDomain<FactSubject> given = NumericDomain.top();
        for (Map.Entry<FactSubject, Bounds> one : kept.at(root, terms).entrySet()) {
            Map<FactSubject, Granularity> spacing =
                    terms.kindsOf(NumericDomain.LinearForm.atom(one.getKey()));
            if (!spacing.isEmpty()) {
                given = given.assuming(one.getKey(), one.getValue(), spacing);
            }
        }
        NumericDomain<FactSubject> read =
                DerivedNumericFacts.refine(given, terms, answered.coefs().keySet());
        Bounds bounds = read.isBottom() ? null : read.boundsOf(answered);
        return bounds == null || bounds.saysNothing() ? Map.of()
                : Map.of(FieldDomains.THE_VALUE, bounds);
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
