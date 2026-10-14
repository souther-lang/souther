package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ARuleNoReadingTakesIn;
import souther.compiler.check.DeclaredBounds;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.Shape;
import souther.compiler.meta.ModulePath;
import souther.compiler.numeric.Towards;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.ItemAssessment;
import souther.compiler.query.ReadAs;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;

import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A set holds each value of its element once and a map each of its keys once, so neither holds
 * more than there are of those, and the points past that number are owed no row.
 *
 * <p>Nothing in the model writes the end down. It is a fact about the type, and the points beyond
 * it are refused as the points beyond an invariant are — where a search for a row there would
 * otherwise come back with nothing and leave the point open.
 */
class AContainerHoldsNoMoreThanItsElementsHaveValuesTest {

    private static final String TYPES = """
            data Service = Insurance | Support | Security
            data Opt = { v: Bool? }
            data Pair = { a: Bool, b: Service }
            data Slot = Int
              invariant value >= 1 && value <= 5
            data Picked = Set<Service>
            data Tagged = { n: Int }
            data Plain
            data Payload = Plain | Tagged
            data Short = List<Bool>
              invariant List.length(value) <= 2
            data Basket = { choices: List<Service> }
              invariant List.length(choices) == 3
              invariant List.allDistinctBy(x -> x, choices)
            data Order = List<Service>
              invariant List.length(value) == 3
              invariant List.allDistinctBy(x -> x, value)
            data Code = String
              invariant value == "a" || value == "b"
            data Twice = String
              invariant value == "a" || value == "a"
            data Narrow = Code
              invariant value.value /= "a"
            data Wrapped = Code
            data Kept = Code
              invariant value.value /= "z"
            data Item = { code: Code, active: Bool }
            data Few = Service
              invariant value == Support || value == Security
            data Pick = { s: Service, n: Bool }
              invariant s == Support || s == Security
            data Odd = Int
              invariant value == 1 || value == 3 || value == 7
            data Loose = String
              invariant (value == "a" || value == "b") && %s
            """.formatted(ARuleNoReadingTakesIn.about("value"));

    /**
     * A list kept apart is told apart by its order as well, so the lists of the three cases each
     * once are every order of them, and a set of all of them is built.
     *
     * <p>Whether the list is kept apart by the record holding it or by a name it wears is one
     * question, read the same way as the list built at a count reads it.
     */
    @Test
    void aSetOfListsKeptApartIsBuiltFromEveryOrderOfThem() {
        for (String type : List.of("Basket", "Order")) {
            BorderAssessment line = lineOf(MODEL.formatted(TYPES, "Set<" + type + ">",
                    "Set.size(s)", 6), "p", "6");

            assertTrue(line.items().get(new DomainPoint.AtTheLine())
                    instanceof ItemAssessment.Owed owed
                    && owed.searches().each().stream()
                            .anyMatch(ItemAssessment.Attempt.Certified.class::isInstance),
                    () -> type + " " + line.items().get(new DomainPoint.AtTheLine()));
        }
    }

    private static final String MODEL = """
            module p
            %s
            behavior f : (s: %s) -> Int
            let f (s) = if %s == %d then 1 else 2
            """;

    /** Each with the number of values of what it holds apart, worked out by hand. */
    @Test
    void thePointsPastHowManyThereAreAreRefused() {
        record Case(String type, String size, int most) {}
        for (Case each : List.of(
                new Case("Set<Service>", "Set.size(s)", 3),
                new Case("Set<Bool>", "Set.size(s)", 2),
                // A record's optional field: none, or one of two.
                new Case("Set<Opt>", "Set.size(s)", 3),
                // The product of its fields.
                new Case("Set<Pair>", "Set.size(s)", 6),
                // The sets of a two-valued element.
                new Case("Set<Set<Bool>>", "Set.size(s)", 4),
                // And of a three-valued one, among which are sets no run of the values makes.
                new Case("Set<Set<Service>>", "Set.size(s)", 8),
                // The lists of a two-valued element no longer than two.
                new Case("Set<Short>", "Set.size(s)", 7),
                // The rules of the element's own declaration.
                new Case("Set<Slot>", "Set.size(s)", 5),
                new Case("Picked", "Set.size(s.value)", 3),
                new Case("Map<Service, Int>", "Map.size(s)", 3),
                // The values its rules name, which is a count of them and not of how they are
                // written, under every name the element wears, and of a number as of a string.
                new Case("Set<Code>", "Set.size(s)", 2),
                new Case("Map<Code, Int>", "Map.size(s)", 2),
                new Case("Set<Twice>", "Set.size(s)", 1),
                new Case("Set<Narrow>", "Set.size(s)", 1),
                // A name over it reads the rules of the name beneath, whether or not it writes
                // any of its own, so both values are offered under it.
                new Case("Set<Wrapped>", "Set.size(s)", 2),
                new Case("Set<Kept>", "Set.size(s)", 2),
                new Case("Set<Odd>", "Set.size(s)", 3),
                // Whatever the shape: cases of an enumeration its rules hold to a few, and a
                // record whose rules hold one field to a few of them, built from those alone.
                new Case("Set<Few>", "Set.size(s)", 2),
                new Case("Set<Pick>", "Set.size(s)", 4),
                // Beside a rule nothing reads, which may refuse one of them and add none.
                new Case("Set<Loose>", "Set.size(s)", 2))) {
            BorderAssessment line = lineOf(MODEL.formatted(TYPES, each.type(), each.size(),
                    each.most()), "p", Integer.toString(each.most()));

            assertEquals(new ItemAssessment.NotOwed(NotOwedReason.THE_RULES_REFUSE_IT),
                    line.items().get(new DomainPoint.BesideTheLine(Towards.ABOVE)), each.type());
            assertEquals(new ItemAssessment.NotOwed(NotOwedReason.THE_RULES_REFUSE_IT),
                    line.items().get(new DomainPoint.InTheRegion(Towards.ABOVE)), each.type());
            // The number itself is one such a value holds, so the end refuses nothing short of it,
            // and a value holding that many is built: every value of what it holds apart, once.
            assertTrue(line.items().get(new DomainPoint.AtTheLine())
                    instanceof ItemAssessment.Owed owed
                    && owed.searches().each().stream()
                            .anyMatch(ItemAssessment.Attempt.Certified.class::isInstance),
                    () -> each.type() + " " + line.items().get(new DomainPoint.AtTheLine()));
            assertTrue(line.items().get(new DomainPoint.BesideTheLine(Towards.BELOW))
                    instanceof ItemAssessment.Owed, each.type());
        }
    }

    private static final String GUARDED = """
            module p
            %s
            behavior f : (s: %s) -> Int
            let f (s) = {
                guard %s else 0

                1
            }
            """;

    /**
     * A guard asking a set for more than its element has values is one no row goes past, and each
     * way past it is said as the rules leaving no value that way — not as a way nothing here could
     * hold a row to, which would leave an author looking for a row nobody can write.
     *
     * <p>Both ways of writing that, and none of the guards a row does go past: as many as there
     * are, fewer, and a set of an element with no end of values. A row going past one of those is
     * looked for and offered, and no way past it is said to be one the rules leave nothing on.
     */
    @Test
    void aGuardAskingForMoreValuesThanThereAreIsOneTheRulesLetNoRowPast() {
        RepairShortfall.WayPast leftNoValue = new RepairShortfall.WayPast.NotSearchable(
                RepairShortfall.Barrier.THE_RULES_LEAVE_NO_VALUE_THAT_WAY);
        record Case(String type, String guard, boolean past) {}
        for (Case each : List.of(
                new Case("Set<Code>", "Set.size(s) >= 3", false),
                new Case("Set<Code>", "Set.size(s) > 2", false),
                new Case("Set<Bool>", "Set.size(s) >= 3", false),
                new Case("Set<Code>", "Set.size(s) >= 2", true),
                new Case("Set<Code>", "Set.size(s) <= 2", true),
                new Case("Set<Code>", "Set.size(s) < 2", true),
                new Case("Set<String>", "Set.size(s) >= 3", true))) {
            List<FillResult.Offer> offers =
                    offersOf(GUARDED.formatted(TYPES, each.type(), each.guard()));
            String said = each.type() + " " + each.guard();
            List<RepairShortfall> stops = offers.stream().map(FillResult.Offer::stop)
                    .filter(Objects::nonNull).toList();
            if (each.past()) {
                assertTrue(offers.stream().anyMatch(offer -> offer.stop() == null),
                        () -> said + ": a row goes past it " + offers);
                for (RepairShortfall stop : stops) {
                    assertTrue(stop.came() instanceof RepairShortfall.AtTheGuard.NoWayPast(var ways)
                            && ways.stream().noneMatch(leftNoValue::equals), () -> said + stop);
                }
            } else {
                assertFalse(stops.isEmpty(), () -> said + ": rows stop at the guard");
                assertEquals(offers.size(), stops.size(), () -> said + ": none goes past");
                for (RepairShortfall stop : stops) {
                    assertTrue(stop.came() instanceof RepairShortfall.AtTheGuard.NoWayPast(var ways)
                            && ways.stream().allMatch(leftNoValue::equals), () -> said + stop);
                }
            }
        }
    }

    /**
     * A record holding such a value is built twice over for a count of the records meeting a
     * statement about another of its fields: the two differ at the value, which the statement
     * says nothing of, and each is one the record's rules leave.
     */
    @Test
    void recordsMeetingAStatementDifferAtAValueTheStatementDoesNotRead() {
        record Case(String type, String count) {}
        for (Case each : List.of(
                new Case("Set<Item>", "Set.size(Set.filter(x -> x.active, s))"),
                // The values the record's rules leave its field, which are not the first of its
                // type's: a value of each kind of the type was one the record refuses.
                new Case("Set<Pick>", "Set.size(Set.filter(x -> x.n, s))"),
                new Case("List<Pick>", "List.length(List.filter(x -> x.n, s))"))) {
            BorderAssessment line =
                    lineOf(MODEL.formatted(TYPES, each.type(), each.count(), 2), "p", "2");

            assertTrue(line.items().get(new DomainPoint.AtTheLine())
                    instanceof ItemAssessment.Owed owed
                    && owed.searches().each().stream()
                            .anyMatch(ItemAssessment.Attempt.Certified.class::isInstance),
                    () -> each.type() + " " + line.items().get(new DomainPoint.AtTheLine()));
        }
    }

    /** Every row offered for {@code f}, with what stopped it where something did. */
    private static List<FillResult.Offer> offersOf(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, Adequacy.Filling> all = Adequacy.generatedOf(compilation.db(), "p");
        assertNotNull(all, "the model under test compiles");
        return all.get("f").composed().offers();
    }

    /**
     * A list holds a value over again, and an element with a number in it has no end of values, so
     * neither says where the size stops.
     */
    @Test
    void whatMayRepeatOrHasNoEndOfValuesRefusesNothing() {
        record Case(String type, String size) {}
        for (Case each : List.of(
                new Case("List<Service>", "List.length(s)"),
                new Case("List<Code>", "List.length(s)"),
                new Case("Set<String>", "Set.size(s)"),
                new Case("Set<Payload>", "Set.size(s)"),
                new Case("Set<Int>", "Set.size(s)"),
                new Case("Map<String, Service>", "Map.size(s)"))) {
            BorderAssessment line =
                    lineOf(MODEL.formatted(TYPES, each.type(), each.size(), 3), "p", "3");

            assertTrue(line.items().get(new DomainPoint.BesideTheLine(Towards.ABOVE))
                    instanceof ItemAssessment.Owed, each.type());
            // And three of them are built, a sum's from the values of each of its cases.
            assertTrue(line.items().get(new DomainPoint.AtTheLine())
                    instanceof ItemAssessment.Owed owed
                    && owed.searches().each().stream()
                            .anyMatch(ItemAssessment.Attempt.Certified.class::isInstance),
                    () -> each.type() + " " + line.items().get(new DomainPoint.AtTheLine()));
        }
    }

    /**
     * A set of maps is built from maps holding different entries at one size, as a set of sets
     * is from different few: one map per size runs out at how many sizes there are, and one per
     * few keys at how many few the keys have, which is fewer than ten.
     */
    @Test
    void aSetOfMapsIsBuiltFromMapsOfOneSizeHoldingDifferentEntries() {
        BorderAssessment line = lineOf(MODEL.formatted(TYPES, "Set<Map<Service, Bool>>",
                "Set.size(s)", 10), "p", "10");

        assertTrue(line.items().get(new DomainPoint.AtTheLine())
                instanceof ItemAssessment.Owed owed
                && owed.searches().each().stream()
                        .anyMatch(ItemAssessment.Attempt.Certified.class::isInstance),
                () -> String.valueOf(line.items().get(new DomainPoint.AtTheLine())));
    }

    private static final String PAST_THE_FIGURES = """
            module p
            data Huge = List<Bool>
              invariant List.length(value) >= 65
            data Long = String
              invariant String.length(value) >= 4097
            data Wide = Map<String, Bool>
              invariant Map.size(value) >= 65
            behavior f : (s: Set<Huge>) -> Int
            let f (s) = if Set.size(s) == 2 then 1 else 0
            """;

    // Every way a value is built at a count asks the figure a proposal is held to: what an
    // element is offered, a string stepped from its floor, and a collection filled to what its
    // rules ask. Asked by one of them alone, the others built past it.

    @Test
    void noCollectionAnElementIsOfferedHoldsMoreThanAProposalHolds() {
        RuleReadingContext reading = pastTheFigures();
        // Asked for more than the figure, since a set or a map is as large as the values it is
        // made from and those are as many as are asked for.
        int many = CompositionBudget.ELEMENTS_A_PROPOSAL_HOLDS.maximum() + 2;
        for (String type : List.of("Huge", "Wide")) {
            for (FixtureTemplate each : Witnesses.distinctValuesOf(declared(type), many,
                    reading, Set.of())) {
                assertTrue(each.text().split(", ").length
                        <= CompositionBudget.ELEMENTS_A_PROPOSAL_HOLDS.maximum(),
                        () -> type + " " + each.text().length());
            }
        }
    }

    @Test
    void noStringAnElementIsOfferedHoldsMoreThanAProposalHolds() {
        for (FixtureTemplate each : Witnesses.distinctValuesOf(declared("Long"), 4,
                pastTheFigures(), Set.of())) {
            assertTrue(each.text().length() <= CompositionBudget.CHARACTERS_A_PROPOSAL_HOLDS
                    .maximum() + "Long(\"\")".length(), () -> each.text().length() + " long");
        }
    }

    @Test
    void aCollectionFilledToItsFloorIsNotBuiltPastWhatAProposalHolds() {
        assertNull(Witnesses.holding(new Shape.Sequence(Shape.Sequence.Kind.LIST, Type.BOOL),
                List.of(), List.of(), List.of(), new DeclaredBounds.CountRange(
                        CompositionBudget.ELEMENTS_A_PROPOSAL_HOLDS.maximum() + 1,
                        Integer.MAX_VALUE), pastTheFigures()));
    }

    private static RuleReadingContext pastTheFigures() {
        Compilation compilation = Compilation.ofSource(PAST_THE_FIGURES, "Main");
        compilation.answerEverything();
        return RuleReadingContext.unshared(RuleReadings.of(compilation, "p"),
                ReadAs.THE_COMPILATION_DOES);
    }

    private static Type declared(String name) {
        return Type.ref(TypeSymbols.declared(new TypeKey("p", name)));
    }

    private static final String SERVICES = """
            module lib.s exposing ( Service )
            data Service = Insurance | Support | Security
            """;

    private static final String SERVICES_AND_ONE_MORE = """
            module lib.s exposing ( Service )
            data Service = Insurance | Support | Security | Roadside
            """;

    private static final String PICKING = """
            module app.p
            import lib.s ( Service )
            behavior f : (s: Set<Service>) -> Int
            let f (s) = if Set.size(s) == 3 then 1 else 2
            """;

    /** A declaration another module makes is counted where it is made. */
    @Test
    void anImportedElementIsCountedAsItsModuleDeclaresIt() {
        Compilation compilation =
                Compilation.ofSources(List.of(SERVICES, PICKING), ModulePath.EMPTY);

        assertEquals(new ItemAssessment.NotOwed(NotOwedReason.THE_RULES_REFUSE_IT),
                lineOf(compilation, "app.p", "3").items()
                        .get(new DomainPoint.BesideTheLine(Towards.ABOVE)));
    }

    /**
     * And an edit to that declaration reaches the end it gave, through the count.
     *
     * <p>A fourth case leaves a set of four to be written, so the point beside the line is owed a
     * row again. Kept from a reading made before the edit, it would still be refused.
     */
    @Test
    void anEditToTheElementMovesTheEnd() {
        Compilation compilation = Compilation.ofDocuments(
                Map.of("s", SERVICES, "p", PICKING), Set.of(), ModulePath.EMPTY);
        assertEquals(new ItemAssessment.NotOwed(NotOwedReason.THE_RULES_REFUSE_IT),
                lineOf(compilation, "app.p", "3").items()
                        .get(new DomainPoint.BesideTheLine(Towards.ABOVE)));

        compilation.update(Map.of("s", SERVICES_AND_ONE_MORE, "p", PICKING), Set.of());

        assertTrue(lineOf(compilation, "app.p", "3").items()
                .get(new DomainPoint.BesideTheLine(Towards.ABOVE)) instanceof ItemAssessment.Owed);
    }

    private static BorderAssessment lineOf(String model, String module, String value) {
        return lineOf(Compilation.ofSource(model, "Main"), module, value);
    }

    private static BorderAssessment lineOf(Compilation compilation, String module, String value) {
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, List<BorderAssessment>> read = Adequacy.readingsOf(compilation.db(), module);
        assertNotNull(read, "the model under test compiles");
        List<BorderAssessment> lines = read.get("f");
        assertNotNull(lines, "f was measured");
        for (BorderAssessment border : lines) {
            if (border.value().equals(value)) {
                return border;
            }
        }
        throw new AssertionError("no line at " + value + " among " + lines);
    }
}
