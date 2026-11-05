package souther.compiler.query;

import org.junit.jupiter.api.Test;

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
 * author's line no row meets.
 *
 * <p>{@code check(if a > 0 then a else 11)} reads {@code x <= 10} at {@code a = 10}, where it stands
 * at the author's points, and at {@code a = 0}, where the caller's choice turns the comparison and
 * the reading is not shown to be a place of the line at all. The second owes nothing and holds the
 * points of the line's kinds open. What a row there shows is about those points and no others, so a
 * search there is worth making where one of them is unmet and is work nobody is owed where a row
 * already meets all of them.
 *
 * <p>Held against what the obligations say after the readings are put together, which is the
 * answer the search is made for: the points a row meets there are the ones a search here may skip.
 */
class ASearchIsMadeOnlyWhereWhatItFindsCanBeOwedTest {

    private static final String MODULE = "example.heldopen";

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
        List<Item> held = itemsOf(compilation, AuthoredPlacement.NotShown.class);
        assertFalse(held.isEmpty(), "the reading at nought has points worth a value");
        for (Item each : held) {
            assertTrue(each.owed().searches().ran(),
                    () -> each + " holds open a point no row meets, so a value is built there");
        }
        assertSearchedExactlyWhereSomethingIsUnmet(compilation);
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
        List<Item> held = itemsOf(compilation, AuthoredPlacement.NotShown.class);
        assertFalse(held.isEmpty(), "the reading at nought has points worth a value");
        for (Item each : held) {
            assertFalse(each.owed().searches().ran(),
                    () -> each + " holds open only points a row meets");
            assertTrue(each.owed().searches().unneeded(),
                    () -> each + " says it was left unsearched, not that a search found nothing");
        }
        assertSearchedExactlyWhereSomethingIsUnmet(compilation);
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
        List<Item> held = itemsOf(compilation, AuthoredPlacement.NotShown.class);
        assertTrue(held.stream().anyMatch(each -> each.owed().searches().ran()),
                () -> "something the reading at nought holds open is unmet: " + held);
        assertTrue(held.stream().anyMatch(each -> each.owed().searches().unneeded()),
                () -> "and something it holds open is met: " + held);
        assertSearchedExactlyWhereSomethingIsUnmet(compilation);
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
        List<Item> none = itemsOf(compilation, AuthoredPlacement.NoPlaceOfTheLine.class);
        assertFalse(none.isEmpty(), "the reading at nought has points worth a value");
        for (Item each : none) {
            assertTrue(each.owed().searches().unneeded(),
                    () -> each + " is about no point of the author's line");
        }
        assertSearchedExactlyWhereSomethingIsUnmet(compilation);
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
        List<Item> held = itemsOf(compilation, AuthoredPlacement.NotShown.class);
        assertFalse(held.isEmpty(), "the reading at nought has points worth a value");
        for (Item each : held) {
            assertFalse(each.reading().border().about(each.at()).isEmpty(),
                    () -> each + " holds points of the author's line open");
            assertTrue(each.owed().searches().unneeded(),
                    () -> each + " holds open only points nobody owes");
        }
        assertSearchedExactlyWhereSomethingIsUnmet(compilation);
    }

    /**
     * Every point worth a value, of every reading: searched exactly where some author's point a row
     * there is about is one the obligations owe and say no row meets, and left unneeded everywhere
     * else.
     */
    private static void assertSearchedExactlyWhereSomethingIsUnmet(Compilation compilation) {
        Set<BorderObligationPoint> unmet = unmetAfterTheReadingsArePutTogether(compilation);
        for (Item each : itemsOf(compilation, AuthoredPlacement.class)) {
            boolean reaches = each.reading().border().about(each.at()).stream()
                    .anyMatch(owed -> unmet.contains(owed.point()));
            assertEquals(reaches, each.owed().searches().ran(),
                    () -> each + " is searched where what it finds can be owed, unmet: " + unmet);
            assertEquals(!reaches, each.owed().searches().unneeded(),
                    () -> each + " says it was left unsearched exactly where it was");
        }
    }

    /** The points owed and met by no row, as the obligations say once the lines are searched. */
    private static Set<BorderObligationPoint> unmetAfterTheReadingsArePutTogether(
            Compilation compilation) {
        List<BorderObligationPointAssessment> points = compilation.db().ask(
                new Adequacy.Obligations(MODULE, new GenerationScope.Behavior("admit"),
                        HowALineIsRead.VALUES_COMPOSED)).value();
        assertNotNull(points, "the behavior's obligations are gathered");
        return points.stream().filter(each -> !each.owed().hasRowWitness())
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

    /** Every point worth a value of every searched reading placed as {@code placed}. */
    private static List<Item> itemsOf(Compilation compilation,
                                      Class<? extends AuthoredPlacement> placed) {
        List<BorderAssessment> searched = compilation.db()
                .ask(new Adequacy.BoundarySearch(MODULE, "admit")).value();
        assertNotNull(searched, "the lines of the behavior were searched");
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

    private static Compilation analysed(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }
}
