package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.ast.Hir;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Compilation;
import souther.compiler.query.Front;
import souther.compiler.query.Shapes;
import souther.compiler.types.TypeSymbol;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A count handed what opening a name found when the name was answered comes to exactly what it
 * would have opening the name all the way down itself.
 *
 * <p>Exactly, proofs included. Which proof a count of none carries is part of the count — the store
 * compares counts to decide what to work out again, and a component that was risen through reads
 * the proofs to decide which of its members were shown anything. So the counts are held equal as
 * values and not as bounds.
 *
 * <p>The models are the places the two could part: lacks at more than one depth of a chain, where
 * the proof carried is the deepest one; a chain ending in a name that is not worn over a value; rules
 * of the reader reaching what the chain ends in; and a chain crossing out of the module it starts
 * in, which is the one a compilation answers a component at a time.
 */
class WhatANameOpensOntoIsHandedOnAndNotOpenedAgainTest {

    private static final String MODULE = "demo";

    private static Map<TypeSymbol, Cardinality> countsAlike(Map<String, String> documents) {
        Compilation c = Compilation.ofDocuments(
                new LinkedHashMap<>(documents), Set.of(), ModulePath.EMPTY);
        c.answerEverything();
        List<Hir.Def> declared = c.module(MODULE).defs().stream()
                .map(each -> each.declaration().node()).toList();
        RuleReadingSource source = Shapes.ruleReading(c.db(), MODULE).value();
        ReadingPolicy policy = c.db().ask(new Front.Reading()).value();

        Map<TypeSymbol, Cardinality> opened =
                CountsByComponent.openingEveryName(declared, source, policy).all();
        assertEquals(opened, CountsByComponent.of(declared, source, policy).all(),
                "handed on, a count came to something opening every name would not have");
        Map<TypeSymbol, Cardinality> stored =
                new LinkedHashMap<>(c.db().ask(new Shapes.CardinalitiesOf(MODULE)).value());
        stored.keySet().retainAll(opened.keySet());
        assertEquals(opened, stored,
                "the store came to something opening every name would not have");
        return opened;
    }

    private static Map<TypeSymbol, Cardinality> countsAlike(String source) {
        return countsAlike(Map.of("demo.sou", source));
    }

    private static Cardinality named(Map<TypeSymbol, Cardinality> counts, String name) {
        return counts.entrySet().stream().filter(each -> each.getKey().name().equals(name))
                .map(Map.Entry::getValue).findFirst().orElseThrow();
    }

    /**
     * What a set's element has none of is the lack at the bottom of the chain and not the name the
     * element is written as: every name above it has none because that one has none.
     *
     * <p>In a set because an element is read under no rule of the set's own, so what the chain ends
     * in comes to nothing in particular and the names are what decide which proof is carried.
     */
    @Test
    void lacksAtEveryDepthCarryTheDeepestOne() {
        Map<TypeSymbol, Cardinality> counts = countsAlike("""
                module demo exposing ( Several )

                data Bad = Int
                    invariant no = value >= 2 && value <= 1
                data A = Bad
                data B = A
                data C = B
                data Several =Set<C>
                    invariant several = Set.size(value) >= 1
                """);

        assertEquals(List.of(new Emptiness.TheNameHasNone(declaredIn(counts, "Bad"))),
                namesIn(named(counts, "Several").why()),
                "the model is no longer about the deepest of several lacks");
    }

    /** A chain ending in a record stops there: the record is read by its name and not opened. */
    @Test
    void aChainEndingInANameThatWearsNoValue() {
        Map<TypeSymbol, Cardinality> counts = countsAlike("""
                module demo exposing ( Several )

                data Bad = Int
                    invariant no = value >= 2 && value <= 1
                data Holder = { bad: Bad }
                data Outer = Holder
                data Top = Outer
                data Several =Set<Top>
                    invariant several = Set.size(value) >= 1
                """);

        assertEquals(List.of(new Emptiness.TheNameHasNone(declaredIn(counts, "Holder"))),
                namesIn(named(counts, "Several").why()),
                "the model is no longer about a chain ending in a record");
    }

    /** What the chain ends in is read under the reader's own rules, so a set the reader asks for
     *  two of is short of values the chain's names never said anything about. */
    @Test
    void theReadersRulesReachWhatTheChainEndsIn() {
        Map<TypeSymbol, Cardinality> counts = countsAlike("""
                module demo exposing ( Pair, Wide )

                data One = Int
                    invariant only = value >= 1 && value <= 1
                data A = One
                data B = A
                data Pair = Set<B>
                    invariant two = Set.size(value) >= 2
                data Wide = Int
                    invariant wide = value >= 1 && value <= 9
                data C = Wide
                data D = C
                data Holder = { d: D }
                """);

        assertTrue(named(counts, "Pair").none(),
                "the model is no longer about a reader's rule reaching the end of a chain");
        assertEquals(Cardinality.atMost(9), named(counts, "Holder"),
                "the model is no longer about a chain that narrows what it ends in");
    }

    /** Each name wrapping a collection of the one before: below the first collection nothing is
     *  read under a rule, and a lack at the bottom is still the one carried. */
    @Test
    void aChainOfNamesEachWrappingACollectionOfTheOneBefore() {
        Map<TypeSymbol, Cardinality> counts = countsAlike("""
                module demo exposing ( Several )

                data Bad = Int
                    invariant no = value >= 2 && value <= 1
                data A = Bad
                data B = List<A>
                data C = Set<B>
                data D = C
                data Several = Set<D>
                    invariant several = Set.size(value) >= 3
                """);

        assertTrue(named(counts, "Several").none(),
                "the model is no longer about a lack read through collections");
    }

    /** The chain the store answers one component at a time, crossing out of the module it is
     *  read from. */
    @Test
    void aChainCrossingOutOfTheModuleItIsReadFrom() {
        Map<String, String> documents = new LinkedHashMap<>();
        documents.put("other.sou", """
                module other exposing ( C )

                data Bad = Int
                    invariant no = value >= 2 && value <= 1
                data A = Bad
                data B = A
                data C = B
                """);
        documents.put("demo.sou", """
                module demo exposing ( Several )

                import other ( C )

                data D = C
                data E = D
                data Several =Set<E>
                    invariant several = Set.size(value) >= 1
                """);
        Map<TypeSymbol, Cardinality> counts = countsAlike(documents);

        assertEquals(List.of(new Emptiness.TheNameHasNone(declaredIn(counts, "Bad"))),
                namesIn(named(counts, "Several").why()),
                "the model is no longer about a lack in another module");
    }

    private static TypeSymbol declaredIn(Map<TypeSymbol, Cardinality> counts, String name) {
        return counts.keySet().stream().filter(each -> each.name().equals(name)).findFirst()
                .orElseThrow();
    }

    /** The proofs that stop at a name, wherever in {@code why} they stand. */
    private static List<Emptiness.TheNameHasNone> namesIn(Emptiness why) {
        return switch (why) {
            case Emptiness.TheNameHasNone it -> List.of(it);
            case Emptiness.AtAField it -> namesIn(it.under());
            case Emptiness.NonEmptyCollectionWithNoElement it -> namesIn(it.element());
            default -> List.of();
        };
    }
}
