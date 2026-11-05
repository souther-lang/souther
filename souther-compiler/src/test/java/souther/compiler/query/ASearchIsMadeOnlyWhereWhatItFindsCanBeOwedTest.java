package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.meta.ModulePath;
import souther.compiler.partition.AuthoredPlacement;
import souther.compiler.partition.BorderObligationPoint;
import souther.compiler.partition.DomainPoint;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A value is built at a point of a reading only where what it shows can reach a point of the
 * author's line that an account of the module keeps and no row meets.
 *
 * <p>{@code check(if a > 0 then a else 11)} reads {@code x <= 10} at {@code a = 10}, where it stands
 * at the author's points, and at {@code a = 0}, where the caller's choice turns the comparison and
 * the reading is not shown to be a place of the line at all. The second owes nothing and holds the
 * points of the line's kinds open. What a row there shows is about those points and no others, so a
 * search there is worth making where one of them is unmet and is work nobody is owed where a row
 * already meets all of them.
 *
 * <p>Held against what the module's obligations say after the readings are put together, which is
 * the answer the search is made for: the points kept and met by no row there are the ones a search
 * here is made for.
 */
class ASearchIsMadeOnlyWhereWhatItFindsCanBeOwedTest {

    private static final String HELD_OPEN = "example.heldopen";

    private static final String MODEL = """
            module example.heldopen

            behavior admit : (a: Int) -> Bool
            let admit (a) = check(if a > 0 then a else 11)

            let check (x: Int): Bool = x <= 10
            """;

    /** With no rows, every point of the reading at nought is unmet, and every one is searched. */
    @Test
    void aReadingNotShownToBeOfTheLineIsSearchedWhereThePointsItHoldsOpenAreUnmet() {
        Compilation compilation = analysed(MODEL);
        List<Item> held = itemsOf(compilation, HELD_OPEN, "admit", AuthoredPlacement.NotShown.class);
        assertFalse(held.isEmpty(), "the reading at nought has points worth a value");
        for (Item each : held) {
            assertTrue(each.owed().searches().ran(),
                    () -> each + " holds open a point no row meets, so a value is built there");
        }
        assertSearchedExactlyWhereSomethingIsUnmet(compilation, HELD_OPEN);
    }

    /**
     * With a row at each of the points of the line, nothing a search of the reading at nought finds
     * is about a point a row does not already meet, and it is not searched — and it says so.
     */
    @Test
    void aReadingNotShownToBeOfTheLineIsNotSearchedWhereEveryPointItHoldsOpenIsMet() {
        Compilation compilation = analysed(MODEL + """

                example admit
                    | (-5) -> true
                    | (10) -> true
                    | (11) -> false
                    | (20) -> false
                """);
        List<Item> held = itemsOf(compilation, HELD_OPEN, "admit", AuthoredPlacement.NotShown.class);
        assertFalse(held.isEmpty(), "the reading at nought has points worth a value");
        for (Item each : held) {
            assertFalse(each.owed().searches().ran(),
                    () -> each + " holds open only points a row meets");
            assertTrue(each.owed().unneeded(),
                    () -> each + " says it was left unsearched, not that a search found nothing");
        }
        assertSearchedExactlyWhereSomethingIsUnmet(compilation, HELD_OPEN);
    }

    /**
     * Between the two: a row at the line alone meets the author's point at it, and the reading at
     * nought is searched beside its line and not at it.
     */
    @Test
    void aPointHeldOpenIsSearchedForWhatIsUnmetAndNotForWhatIsMet() {
        Compilation compilation = analysed(MODEL + """

                example admit
                    | (10) -> true
                """);
        List<Item> held = itemsOf(compilation, HELD_OPEN, "admit", AuthoredPlacement.NotShown.class);
        assertTrue(held.stream().anyMatch(each -> each.owed().searches().ran()),
                () -> "something the reading at nought holds open is unmet: " + held);
        assertTrue(held.stream().anyMatch(each -> each.owed().unneeded()),
                () -> "and something it holds open is met: " + held);
        assertSearchedExactlyWhereSomethingIsUnmet(compilation, HELD_OPEN);
    }

    /**
     * A reading shown to be no place of the author's line owes nothing and holds nothing open, and
     * is not searched even where no row meets anything.
     */
    @Test
    void aReadingShownToBeNoPlaceOfTheLineIsNeverSearched() {
        Compilation compilation = analysed("""
                module example.heldopen

                behavior admit : (a: Int) -> Bool
                let admit (a) = check(if a > 0 then 10 else 11)

                let check (x: Int): Bool = x <= 10
                """);
        List<Item> none =
                itemsOf(compilation, HELD_OPEN, "admit", AuthoredPlacement.NoPlaceOfTheLine.class);
        assertFalse(none.isEmpty(), "the reading at nought has points worth a value");
        for (Item each : none) {
            assertTrue(each.owed().unneeded(),
                    () -> each + " is about no point of the author's line");
        }
        assertSearchedExactlyWhereSomethingIsUnmet(compilation, HELD_OPEN);
    }

    /**
     * Where the caller's choice turns the comparison and the line is crossed nowhere else, the
     * reading at nought holds open points no reading owes. They are in nobody's account, so a
     * search there finds nothing anybody is owed, and none is made.
     */
    @Test
    void aReadingNotShownToBeOfTheLineIsNotSearchedForPointsNobodyOwes() {
        Compilation compilation = analysed("""
                module example.heldopen

                behavior admit : (a: Int) -> Bool
                let admit (a) = check(if a > 0 then a + 20 else a)

                let check (x: Int): Bool = x <= 10
                """);
        List<Item> held = itemsOf(compilation, HELD_OPEN, "admit", AuthoredPlacement.NotShown.class);
        assertFalse(held.isEmpty(), "the reading at nought has points worth a value");
        for (Item each : held) {
            assertFalse(each.reading().border().about(each.at()).isEmpty(),
                    () -> each + " holds points of the author's line open");
            assertTrue(each.owed().unneeded(),
                    () -> each + " holds open only points nobody owes");
        }
        assertSearchedExactlyWhereSomethingIsUnmet(compilation, HELD_OPEN);
    }

    /**
     * A line an {@code invariant} drew is owed once however many behaviors carry the type, and a
     * row written for one of them meets it: {@code hold}, which has no rows, is not searched at
     * the points {@code keep}'s rows meet.
     */
    @Test
    void aPointARowOfAnotherBehaviorMeetsIsNotSearched() {
        Compilation compilation = analysed("""
                module example.both

                data Amount = Int
                    invariant value >= 10

                data Ok = { n: Int }

                behavior keep : (a: Amount) -> Ok
                let keep (a) = Ok { n = a.value }

                behavior hold : (a: Amount) -> Ok
                let hold (a) = Ok { n = a.value }

                example keep
                    | (Amount(10)) -> Ok { n = 10 }
                    | (Amount(50)) -> Ok { n = 50 }
                """);
        List<Item> held = itemsOf(compilation, "example.both", "hold", AuthoredPlacement.class);
        assertFalse(held.isEmpty(), "hold reads the line and has no row at it");
        for (Item each : held) {
            assertTrue(each.owed().unneeded(),
                    () -> each + " is about a point keep's rows meet");
        }
        assertSearchedExactlyWhereSomethingIsUnmet(compilation, "example.both");
    }

    /**
     * A helper called from two arms is one line read twice at one place, and the two are put
     * together as one reading. Left unsearched in both, it is left unsearched as one.
     *
     * <p>{@code check(a)} is read at {@code a = 10} under each arm, and {@code check(a - 1)} reads
     * the same line at {@code a = 11}, where the rows stand. A row there meets the author's point at
     * the line, so neither copy at ten is searched for it.
     */
    @Test
    void aLineReadTwiceAtOnePlaceIsLeftUnsearchedOnceAsBothWere() {
        Compilation compilation = analysed("""
                module example.twice

                behavior hold : (a: Int, b: Bool) -> Bool
                let hold (a, b) =
                    if check(a - 1) then (if b then check(a) else Bool.not(check(a))) else false

                let check (x: Int): Bool = x <= 10

                example hold
                    | (-4, true) -> true
                    | (11, true) -> false
                    | (12, true) -> false
                    | (21, true) -> false
                """);
        List<Item> atTen = itemsOf(compilation, "example.twice", "hold", AuthoredPlacement.class)
                .stream().filter(each -> each.reading().border().label().equals("a = 10")
                        && each.at() instanceof DomainPoint.AtTheLine).toList();
        assertEquals(1, atTen.size(), () -> "the two copies at ten are one reading: " + atTen);
        assertTrue(atTen.getFirst().reading().readAt().inOrder().size() > 1,
                () -> "read at both calls: " + atTen.getFirst().reading().readAt());
        assertTrue(atTen.getFirst().owed().unneeded(),
                () -> atTen.getFirst() + " is about the point the row at eleven meets");
        assertSearchedExactlyWhereSomethingIsUnmet(compilation, "example.twice");
    }

    /**
     * A line another module's declaration drew is that module's to answer for. A behavior here
     * carrying the type reads it with no row at it, and is not searched for it: nothing this
     * module keeps reads what such a search finds.
     */
    @Test
    void aPointAnotherModulesDeclarationOwnsIsNotSearchedHere() {
        Compilation compilation = Compilation.ofSources(List.of("""
                module example.amounts

                data Amount = Int
                    invariant value >= 10
                """, """
                module example.carrying

                import example.amounts ( Amount )

                data Ok = { n: Int }

                behavior hold : (a: Amount) -> Ok
                let hold (a) = Ok { n = a.value }
                """), ModulePath.EMPTY);
        compilation.measure(Adequacy.Asked.fullReport());
        List<Item> held = itemsOf(compilation, "example.carrying", "hold", AuthoredPlacement.class);
        assertFalse(held.isEmpty(), "hold reads the line and has no row at it");
        for (Item each : held) {
            assertTrue(each.owed().unneeded(),
                    () -> each + " is about a point example.amounts owns");
        }
        assertSearchedExactlyWhereSomethingIsUnmet(compilation, "example.carrying");
    }

    /**
     * Every point worth a value, of every reading of every behavior: searched exactly where some
     * author's point a row there is about is one the module keeps and no row meets, and left
     * unneeded everywhere else.
     */
    private static void assertSearchedExactlyWhereSomethingIsUnmet(Compilation compilation,
                                                                   String module) {
        Set<BorderObligationPoint> unmet = unmetAfterTheReadingsArePutTogether(compilation, module);
        Map<String, List<BorderAssessment>> searched =
                Adequacy.searchedBoundariesOf(compilation.db(), module);
        assertNotNull(searched, "the module's lines were searched");
        for (String behavior : searched.keySet()) {
            for (Item each : itemsOf(compilation, module, behavior, AuthoredPlacement.class)) {
                boolean reaches = each.reading().border().about(each.at()).stream()
                        .anyMatch(owed -> unmet.contains(owed.point()));
                assertEquals(reaches, each.owed().searches().ran(),
                        () -> each + " is searched where what it finds is read, unmet: " + unmet);
                assertEquals(!reaches, each.owed().unneeded(),
                        () -> each + " says it was left unsearched exactly where it was");
            }
        }
    }

    /** The points the module keeps and no row meets, as its obligations say once its lines are
     *  searched. */
    private static Set<BorderObligationPoint> unmetAfterTheReadingsArePutTogether(
            Compilation compilation, String module) {
        List<BorderObligationPointAssessment> points = compilation.db().ask(
                new Adequacy.Obligations(module, new GenerationScope.Module(),
                        HowALineIsRead.VALUES_COMPOSED)).value();
        assertNotNull(points, "the module's obligations are gathered");
        return points.stream()
                .filter(each -> each.keptBy(module) && !each.owed().hasRowWitness())
                .map(BorderObligationPointAssessment::point).collect(Collectors.toSet());
    }

    /** One point of one reading worth a value, as the search left it. */
    private record Item(BorderAssessment reading, DomainPoint at, ItemAssessment.Owed owed) {

        @Override
        public String toString() {
            return at + " of " + reading.border().label() + " (" + reading.border().placement()
                    + ")";
        }
    }

    /** Every point worth a value of every searched reading of {@code behavior} placed as
     *  {@code placed}. */
    private static List<Item> itemsOf(Compilation compilation, String module, String behavior,
                                      Class<? extends AuthoredPlacement> placed) {
        List<BorderAssessment> searched = compilation.db()
                .ask(new Adequacy.BoundarySearch(module, behavior)).value();
        assertNotNull(searched, "the lines of " + behavior + " were searched");
        List<Item> out = new ArrayList<>();
        for (BorderAssessment reading : searched) {
            if (!placed.isInstance(reading.border().placement())) {
                continue;
            }
            for (Map.Entry<DomainPoint, ItemAssessment> each : reading.items().entrySet()) {
                if (each.getValue() instanceof ItemAssessment.Owed owed && owed.worthSearching()) {
                    out.add(new Item(reading, each.getKey(), owed));
                }
            }
        }
        return out;
    }

    /** The model, with its rows run: what the search and the obligations read, and nothing else. */
    private static Compilation analysed(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        return compilation;
    }
}
