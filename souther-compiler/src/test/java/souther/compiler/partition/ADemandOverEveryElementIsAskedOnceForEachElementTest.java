package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.check.DeclaredBounds;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.Shape;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeView;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.check.Carrier;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.observe.ElementsTaken;
import souther.compiler.query.ReadAs;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.OptionalInt;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A demand asked under a quantifier over every element of a container is asked once for each
 * element the container was built holding, and not at all where it holds none.
 *
 * <p>Every element of {@code ks} filed in {@code shelf}: what {@code shelf} is handed turns on what
 * {@code ks} was built as. Holding nothing, {@code ks} meets the statement whatever {@code shelf}
 * holds, so {@code shelf} is handed nothing and is not made to hold anything. Holding two keys,
 * {@code ks} meets it only with an entry for each, and {@code shelf} is handed both.
 */
class ADemandOverEveryElementIsAskedOnceForEachElementTest {

    private static final RuleReadingSource NONE =
            RuleReadings.ofNoClauseFiled(Symbols.none(DefaultStdlib.get()));

    private static final RuleReadingContext READING =
            RuleReadingContext.unshared(NONE, ReadAs.THE_COMPILATION_DOES);

    private static final ConditionReportAnchor WHERE =
            new ConditionReportAnchor.WhereTheReadingMetIt("g",
                    new ConditionOccurrence("pick", 0));

    /** What the container holding one or none is said as, which nothing here reads. */
    private static final RowDemand.Relational HOLDING = new RowDemand.Relational(
            new TakenConstraint.Affine(
                    LinearForm.atom(new NumericTerm.ValueOf(TermPath.of("n"))), Rel.GE));

    private static final TermPath KS = TermPath.of("ks");
    private static final TermPath SHELF = TermPath.of("shelf");

    private static ContentsAsked asked(RowDemand.OfACondition demand) {
        return ContentsAsked.of(List.of(new OnTheWay.TakenIn(WHERE, demand)));
    }

    private static ContentsAsked everyKeyFiled() {
        return asked(new RowDemand.ForAll(KS, RowDemand.AnElementMeets.only(List.of(
                new RowDemand.WithinIt(SHELF, true, new RowDemand.KeyedAs(KS.element())))),
                HOLDING));
    }

    /** What {@code ks} handed on, built holding {@code keys}. */
    private static ValuesHandedOn ksBuiltAs(String... keys) {
        List<ValuesHandedOn.Standing> values = new ArrayList<>();
        List<ElementsTaken> elements = new ArrayList<>();
        for (int i = 0; i < keys.length; i++) {
            ElementsTaken at = ElementsTaken.NONE.and(KS, i);
            values.add(new ValuesHandedOn.Standing(at, FixtureTemplate.string(keys[i])));
            elements.add(at);
        }
        return new ValuesHandedOn(Map.of(KS.element(), values), Map.of(), Map.of(KS, elements));
    }

    private static ContentsAsked.Here resolved(ContentsAsked asked, String head,
                                               ValuesHandedOn handed) {
        ContentsAsked.Resolution resolution = asked.resolvedFor(head, handed);
        return assertInstanceOf(ContentsAsked.Resolution.Resolved.class, resolution,
                () -> "what the container is handed is told: " + resolution).here();
    }

    private static List<String> keysEachFiled(ContentsAsked.Here here) {
        ContainerContents contents = here.contentsOf(SHELF, _ -> null);
        assertNotNull(contents, "nothing is read off the shelf's own parameter");
        return contents.keysEachFiled().stream().map(FixtureTemplate::text).toList();
    }

    @Test
    void aListHoldingNoneHandsTheMapNothing() {
        ContentsAsked asked = everyKeyFiled();
        ContentsAsked.Here here = resolved(asked, "shelf", ksBuiltAs());

        assertEquals(List.of(), keysEachFiled(here));
        assertEquals(Set.of(), asked.composedUnder("shelf", here).holdingOne(),
                "the map is not made to hold an entry");
    }

    @Test
    void aListHoldingTwoHandsTheMapAKeyForEach() {
        ContentsAsked asked = everyKeyFiled();
        ContentsAsked.Here here = resolved(asked, "shelf", ksBuiltAs("a", "b"));

        assertEquals(List.of("\"a\"", "\"b\""), keysEachFiled(here));
        assertEquals(Set.of(SHELF), asked.composedUnder("shelf", here).holdingOne());
    }

    /** Asked of the list's own plan, the value read off every element is no position of it. */
    @Test
    void theListIsAskedNothingForTheValueReadOffIt() {
        ContentsAsked asked = everyKeyFiled();

        assertEquals(new ContentsAsked.ToHandOn(Set.of(), Set.of(KS.element()), Set.of(KS)),
                asked.handedOnFrom("ks"));
        assertEquals(Set.of(), asked.composedUnder("ks", resolved(asked, "ks", ksBuiltAs()))
                .read());
        assertEquals(Map.of("shelf", Set.of("ks")), asked.composedAfter());
    }

    /**
     * A value read outside the list, asked for each element of it: handed once for each element,
     * and not at all where the list holds none — so the list is composed before the map.
     */
    @Test
    void aValueReadOutsideTheListIsHandedForEachElementOfIt() {
        TermPath n = TermPath.of("n");
        ContentsAsked asked = asked(new RowDemand.ForAll(KS, RowDemand.AnElementMeets.only(
                List.of(new RowDemand.WithinIt(SHELF, true, new RowDemand.KeyedAs(n)))),
                HOLDING));
        ValuesHandedOn nBuilt = new ValuesHandedOn(Map.of(n, List.of(new ValuesHandedOn.Standing(
                ElementsTaken.NONE, FixtureTemplate.string("x")))), Map.of(), Map.of());

        assertEquals(List.of(), keysEachFiled(resolved(asked, "shelf", ksBuiltAs().and(nBuilt))));
        assertEquals(List.of("\"x\"", "\"x\""),
                keysEachFiled(resolved(asked, "shelf", ksBuiltAs("a", "b").and(nBuilt))));
        assertEquals(Map.of("shelf", Set.of("n", "ks")), asked.composedAfter());
    }

    /**
     * Every element of a list inside the elements of another: each value is the one read in the
     * element it stands in, and two elements standing at the same place in the lines of two
     * orders are two elements.
     */
    @Test
    void aValueIsReadInTheElementOfEveryContainerAroundIt() {
        TermPath os = TermPath.of("os");
        TermPath lines = os.element().then("ls");
        ContentsAsked asked = asked(new RowDemand.ForAll(lines, RowDemand.AnElementMeets.only(
                List.of(new RowDemand.WithinIt(SHELF, true,
                        new RowDemand.KeyedAs(lines.element())))), HOLDING));
        ElementsTaken first = ElementsTaken.NONE.and(os, 0).and(lines, 0);
        ElementsTaken second = ElementsTaken.NONE.and(os, 1).and(lines, 0);
        ElementsTaken third = ElementsTaken.NONE.and(os, 1).and(lines, 1);
        ValuesHandedOn handed = new ValuesHandedOn(Map.of(lines.element(), List.of(
                new ValuesHandedOn.Standing(first, FixtureTemplate.string("a")),
                new ValuesHandedOn.Standing(second, FixtureTemplate.string("b")),
                new ValuesHandedOn.Standing(third, FixtureTemplate.string("c")))), Map.of(),
                Map.of(lines, List.of(first, second, third)));

        assertEquals(List.of("\"a\"", "\"b\"", "\"c\""),
                keysEachFiled(resolved(asked, "shelf", handed)));
    }

    /**
     * The list and the map under one parameter: nothing built yet says how many keys the map is
     * to hold, so it is handed none — and that is kept, so that composing nothing is not taken for
     * there being nothing to compose.
     */
    @Test
    void aDemandOverAContainerOfTheSameParameterIsKeptAsLeftOpen() {
        TermPath input = TermPath.of("input");
        TermPath ks = input.then("ks");
        TermPath shelf = input.then("shelf");
        ContentsAsked asked = asked(new RowDemand.ForAll(ks, RowDemand.AnElementMeets.only(
                List.of(new RowDemand.WithinIt(shelf, true, new RowDemand.KeyedAs(ks.element())))),
                HOLDING));
        ContentsAsked.Here here = resolved(asked, "input", ValuesHandedOn.NONE);

        assertEquals(List.of(), here.given());
        assertEquals(asked.asked(), here.leftOpen());
        assertTrue(here.notComposed().isPresent());
        assertEquals(Optional.empty(), resolved(everyKeyFiled(), "shelf", ksBuiltAs("a"))
                .notComposed(), "a demand handed on leaves nothing open");
    }

    /** Two values read in one element are no one value for it, and are said as that. */
    @Test
    void twoValuesInOneElementAreNoOneValue() {
        ElementsTaken only = ElementsTaken.NONE.and(KS, 0);
        ValuesHandedOn handed = new ValuesHandedOn(Map.of(KS.element(), List.of(
                new ValuesHandedOn.Standing(only, FixtureTemplate.string("a")),
                new ValuesHandedOn.Standing(only, FixtureTemplate.string("b")))), Map.of(),
                Map.of(KS, List.of(only)));

        assertInstanceOf(ContentsAsked.Resolution.Unresolved.class,
                everyKeyFiled().resolvedFor("shelf", handed));
    }

    /**
     * A count of the elements of {@code ks} some entry of {@code shelf} is keyed by, or some
     * element of it is, hands the map its key or the list its element for each of the first so
     * many elements, and keeps out those of the rest.
     */
    @Test
    void aCountOfElementsFiledElsewhereHandsTheOtherContainerTheFirstSoMany() {
        ACountHandedOn keyed = new ACountHandedOn(KS,
                new RowDemand.WithinIt(SHELF, true, new RowDemand.KeyedAs(KS.element())));
        assertEquals(List.of(
                new ContentsAsked.Asked(SHELF, KS.element(), true, true,
                        Optional.of(new ContentsAsked.Around(KS, false, 0, 2))),
                new ContentsAsked.Asked(SHELF, KS.element(), false, true,
                        Optional.of(new ContentsAsked.Around(KS, false, 2, Integer.MAX_VALUE)))),
                keyed.asked(2));
        assertEquals(List.of(new ContentsAsked.Asked(SHELF, KS.element(), false, true,
                        Optional.of(ContentsAsked.Around.over(KS, false)))),
                keyed.asked(0), "none counted, so every key is kept out");

        TermPath others = TermPath.of("others");
        ACountHandedOn held = new ACountHandedOn(KS,
                new RowDemand.WithinIt(others, false, new RowDemand.DifferentFrom(KS.element())));
        assertEquals(new ContentsAsked.Asked(others, KS.element(), false, false,
                Optional.of(new ContentsAsked.Around(KS, false, 0, 1))), held.asked(1).getFirst(),
                "counted where no element of it is the value, so it holds none equal to it");
        assertEquals(new RowDemand.WithinIt(others, true, new RowDemand.SameAs(KS.element())),
                held.denied(), "and not counted where some element of it is");
    }

    /**
     * A count of the elements of {@code items} whose own map is keyed by {@code k}: the map is
     * inside each element, written alike in every one, so the first holding the key and the rest
     * none is no element written alike — and the count hands nothing on.
     */
    @Test
    void aCountOverAContainerInsideTheElementHandsNothingOn() {
        TermPath items = TermPath.of("items");
        TermPath tags = items.element().then("tags");
        RowDemand.WithinIt keyed = new RowDemand.WithinIt(tags, true,
                new RowDemand.KeyedAs(TermPath.of("k")));

        assertEquals(Optional.empty(), ACountHandedOn.of(items, keyed));
        assertTrue(ACountHandedOn.of(KS, new RowDemand.WithinIt(SHELF, true,
                new RowDemand.KeyedAs(KS.element()))).isPresent(), "another container is handed on");
    }

    /**
     * Asked of a run of the elements only, a demand on a container inside the element is not the
     * plan's: the plan writes every element alike. Nothing built says which elements the run is,
     * so it is left open.
     */
    @Test
    void aDemandOnARunOfTheElementsIsNotThePlans() {
        TermPath items = TermPath.of("items");
        TermPath tags = items.element().then("tags");
        ContentsAsked.Asked first = new ContentsAsked.Asked(tags, TermPath.of("k"), true, true,
                Optional.of(new ContentsAsked.Around(items, false, 0, 1)));
        ContentsAsked.Asked every = new ContentsAsked.Asked(tags, TermPath.of("k"), true, true,
                Optional.of(ContentsAsked.Around.over(items, false)));

        assertFalse(first.askedOfThePlan());
        assertTrue(every.askedOfThePlan());
        assertEquals(List.of(first), resolved(new ContentsAsked(List.of(first)), "items",
                ValuesHandedOn.NONE).leftOpen());
    }

    /**
     * Handed the first element counted of two the list was built with: the map is to hold the key
     * of the first and none equal to the second's.
     */
    @Test
    void aCountOfOneOfTwoHandsTheFirstAndKeepsTheSecondOut() {
        ContentsAsked asked = new ContentsAsked(new ACountHandedOn(KS,
                new RowDemand.WithinIt(SHELF, true, new RowDemand.KeyedAs(KS.element())))
                .asked(1));
        ContainerContents contents = resolved(asked, "shelf", ksBuiltAs("a", "b"))
                .contentsOf(SHELF, _ -> null);

        assertNotNull(contents);
        assertEquals(List.of("\"a\""), contents.keysEachFiled().stream()
                .map(FixtureTemplate::text).toList());
        assertEquals(List.of("\"b\""), contents.keysKeptOut().stream()
                .map(FixtureTemplate::text).toList());
    }

    /**
     * The count a container is composed at is the one walked — the one a caller named, where it
     * named one out of several — and not the fewest the search is about.
     */
    @Test
    void theCountComposedIsTheOneWalked() {
        NumericSet notTwo = new NumericSet.AwayFrom(List.of(Count.of(2)));
        assertEquals(OptionalInt.of(1), ACountHandedOn.counted(
                AskedAt.aNumberOutOf(notTwo, Count.of(1), Carrier.WHOLE)));
        assertEquals(OptionalInt.of(0), ACountHandedOn.counted(
                AskedAt.theClass(notTwo, Carrier.WHOLE)));
    }

    private static Shape.Mapping map() {
        return (Shape.Mapping) TypeView.asWritten(new Type.MapOf(Type.STRING, Type.STRING),
                NONE.symbols(), NONE.kinds(), NONE.sums()).shape();
    }

    private static FixtureTemplate built(List<FixtureTemplate> eachFiled,
                                         List<FixtureTemplate> keptOut, int most) {
        return Witnesses.holding(map(), List.of(), List.of(), null, eachFiled, keptOut,
                new DeclaredBounds.CountRange(0, most), READING);
    }

    /** Each key handed is an entry of the map built, and one key handed twice is one entry. */
    @Test
    void theMapIsBuiltWithAnEntryForEachKeyHanded() {
        FixtureTemplate a = FixtureTemplate.string("a");
        FixtureTemplate b = FixtureTemplate.string("b");

        FixtureTemplate both = built(List.of(a, b, a), List.of(), Integer.MAX_VALUE);
        assertNotNull(both);
        assertEquals("[(\"a\", \"x\"), (\"b\", \"x\")]", both.text());
    }

    /** More keys than the rules leave room for, or a key kept out, is no map. */
    @Test
    void keysThatCannotAllStandAreNoMap() {
        FixtureTemplate a = FixtureTemplate.string("a");
        FixtureTemplate b = FixtureTemplate.string("b");

        assertNull(built(List.of(a, b), List.of(), 1));
        assertNull(built(List.of(a), List.of(a), Integer.MAX_VALUE));
    }
}
