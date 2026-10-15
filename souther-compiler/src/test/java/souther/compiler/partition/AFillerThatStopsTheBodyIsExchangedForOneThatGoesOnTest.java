package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A row's value at a position it is not about is exchanged for one that lets the body go on, where
 * the value it was first composed with is what stopped the body at a guard.
 *
 * <p>The row for a class of {@code kind} is about {@code kind}. Composed from the classes alone,
 * {@code amount} stands at the first class it has, which fails {@code amount > 0}, and every such
 * row answers {@code Refused} before {@code kind} is read: the class counts as covered by a row that
 * says nothing about it. Run, the row is seen leaving the guard, and the way into the rest of the
 * block says what {@code amount} has to be for the body to go on.
 *
 * <p>And the row for the class that fails the guard keeps it. That row is about the value the
 * guard refuses, and stopping there is what it is for.
 */
class AFillerThatStopsTheBodyIsExchangedForOneThatGoesOnTest {

    private static final String MODEL = """
            module example.settle

            data Plain
            data Express
            data Kind = Plain | Express

            data Done = { n: Int }
            data Refused

            behavior settle : (kind: Kind, amount: Int) -> Done | Refused
                constructs Done

            let settle (kind, amount) = {
                guard amount > 0 else Refused
                match kind with
                    | Plain -> Done { n = amount }
                    | Express -> Done { n = amount + 500 }
            }
            """;

    /**
     * A guard on a comparison and a truth the body was handed, which no comparison answers.
     *
     * <p>The way past is the comparison holding and the run going down the arm that goes on, which
     * is where the truth is seen. What the arm asks of a row is the condition holding, so the row
     * is composed with both.
     */
    private static final String A_COMPARISON_AND_A_TRUTH = """
            module example.settle

            data Plain
            data Express
            data Kind = Plain | Express

            data Done = { n: Int }
            data Refused

            behavior settle : (kind: Kind, amount: Int, open: Bool) -> Done | Refused
                constructs Done

            let settle (kind, amount, open) = {
                guard amount > 0 && open else Refused
                match kind with
                    | Plain -> Done { n = amount }
                    | Express -> Done { n = amount + 500 }
            }
            """;

    @Test
    void aRowAboutAnotherPositionGoesOnPastAGuardOnAComparisonAndATruth() {
        Map<String, String> rows = rowsOf(A_COMPARISON_AND_A_TRUTH);
        assertEquals("Plain, 1, true", rows.get("kind=Plain"));
        assertEquals("Express, 1, true", rows.get("kind=Express"));
    }

    /** The rows about {@code kind} are past the guard. */
    @Test
    void aRowAboutAnotherPositionGoesOnPastTheGuard() {
        Map<String, String> rows = rowsOf(MODEL);
        assertEquals("Plain, 1", rows.get("kind=Plain"));
        assertEquals("Express, 1", rows.get("kind=Express"));
    }

    /** The row about the class the guard refuses still stops there. */
    @Test
    void aRowAboutTheClassTheGuardRefusesKeepsIt() {
        assertEquals("Plain, 0", rowsOf(MODEL).get("amount=x <= 0"));
    }

    /**
     * A guard on what the elements of a list add up to, read through a helper.
     *
     * <p>No position holds the total, and the amount of an element is not a position anything
     * divides either: the value a row is composed with puts the least amount there is in every
     * element. So what gets a row past the guard is a demand on the list as a whole, and the list
     * is composed to meet it — with what the row's classes ask of each element held in it.
     */
    private static final String A_TOTAL = """
            module example.settle

            data Plain
            data Express
            data Kind = Plain | Express

            data Amount = Int
                invariant value >= 0

            data Self
            data Company
            data Payer = Self | Company

            data Item = { amount: Amount, payer: Payer }

            data Done = { n: Int }
            data Refused

            behavior settle : (kind: Kind, items: List<Item>) -> Done | Refused
                constructs Done

            let total (items: List<Item>): Int = List.sum(List.map(i -> i.amount.value, items))

            let settle (kind, items) = {
                guard total(items) > 0 else Refused
                match kind with
                    | Plain -> Done { n = total(items) }
                    | Express -> Done { n = total(items) + 500 }
            }
            """;

    /** The rows about {@code kind} hold a list whose amounts come to more than nothing. */
    @Test
    void aRowAboutAnotherPositionGoesOnPastAGuardOnATotal() {
        Map<String, String> rows = rowsOf(A_TOTAL);
        assertEquals("Plain, [Item { amount = Amount(1), payer = Self }]", rows.get("kind=Plain"));
    }

    /**
     * And a row about a class of the elements keeps that class in every element while the list is
     * composed to the total.
     */
    @Test
    void aRowAboutAClassOfTheElementsKeepsItWhileTheListComesToTheTotal() {
        assertEquals("Plain, [Item { amount = Amount(1), payer = Company }]",
                rowsOf(A_TOTAL).get("items[*].payer=Company"));
    }

    /**
     * A fork above the guard, which the row goes through the false way and goes on from.
     *
     * <p>Its comparison comes out the false way in the run as the guard's does, and it is not what
     * stopped the row: the row went on past it. Held to it, the row would be sent the other way
     * round a fork that let it go on, and the guard that refused it would be what nothing was held
     * to.
     */
    private static final String A_FORK_ABOVE = """
            module example.settle

            data Plain
            data Express
            data Kind = Plain | Express

            data Done = { n: Int }
            data Refused

            behavior settle : (kind: Kind, earlier: Int, amount: Int) -> Done | Refused
                constructs Done

            let settle (kind, earlier, amount) = {
                let bonus = if earlier > 0 then 100 else 0
                guard amount > 0 else Refused
                match kind with
                    | Plain -> Done { n = amount + bonus }
                    | Express -> Done { n = amount + bonus + 500 }
            }
            """;

    /** The row about {@code kind} is held to the guard's comparison, and goes the same way round
     *  the fork above it as it did. */
    @Test
    void aRowIsHeldToTheGuardThatStoppedItAndNotToAForkAboveIt() {
        assertEquals("Plain, 0, 1", rowsOf(A_FORK_ABOVE).get("kind=Plain"));
    }

    /**
     * A guard that lets the body go on where its comparison comes out false.
     *
     * <p>{@code amount = 0} makes {@code amount <= 0} hold and the guard refuse. What gets a row
     * past is the comparison failing, which a repair that took every guard's comparison to be one
     * that has to hold could not ask for.
     */
    @Test
    void aRowIsHeldToTheWayTheGuardsComparisonHasToComeOut() {
        Map<String, String> rows =
                rowsOf(MODEL.replace("guard amount > 0", "guard Bool.not(amount <= 0)"));
        assertEquals("Plain, 1", rows.get("kind=Plain"));
        assertEquals("Plain, 0", rows.get("amount=x <= 0"), "the row about the refused class");
    }

    private static final String TWO_AMOUNTS = """
            module example.settle

            data Plain
            data Express
            data Kind = Plain | Express

            data Done = { n: Int }
            data Refused

            behavior settle : (kind: Kind, a: Int, b: Int) -> Done | Refused
                constructs Done

            let settle (kind, a, b) = {
                guard CONDITION else Refused
                match kind with
                    | Plain -> Done { n = a + b }
                    | Express -> Done { n = a + b + 500 }
            }
            """;

    /**
     * Both sides of an {@code &&} at once. A row that stops at the first is not past the guard
     * once the first holds — the second refuses it then — so what is asked for is the way whole.
     *
     * <p>The second side on a total, which no class of a position gives a row the way to: held to
     * the first side alone, the search finds nothing past the guard however it walks the classes.
     */
    @Test
    void aWayPastAGuardIsEveryComparisonItTakesAtOnce() {
        String both = A_TOTAL
                .replace("(kind: Kind, items: List<Item>)", "(kind: Kind, a: Int, items: List<Item>)")
                .replace("let settle (kind, items)", "let settle (kind, a, items)")
                .replace("guard total(items) > 0", "guard a > 0 && total(items) > 0");
        assertEquals("Plain, 1, [Item { amount = Amount(1), payer = Self }]",
                rowsOf(both).get("kind=Plain"));
    }

    /** Either side of an {@code ||}, and one is enough: the row is moved at one position. */
    @Test
    void aGuardWithTwoWaysPastIsPassedByOne() {
        assertEquals("Plain, 1, 0",
                rowsOf(TWO_AMOUNTS.replace("CONDITION", "a > 0 || b > 0")).get("kind=Plain"));
    }

    /**
     * A row written against a value the module states keeps it, though the guard refuses it.
     *
     * <p>The value is one the author chose, and what it does to the body is what the row says about
     * it. So the row is looked past only from the value it was written against, and with that value
     * where it stands — a composed amount would get past the guard, and is not what is asked.
     */
    @Test
    void aRowKeepsTheValueTheModelStatesThoughItStopsAtTheGuard() {
        String stating = MODEL + """

                let noAmount: Int = 0
                """;
        assertEquals("Plain, noAmount", rowsOf(stating).get("kind=Plain"));
    }

    /**
     * And a field of it the row is not about stays where it stands, though moving it with the row's
     * own class written beside it would get past the guard.
     */
    @Test
    void aRowKeepsEveryFieldOfTheValueTheModelStatesThatItIsNotAbout() {
        String stating = """
                module example.settle

                data Plain
                data Express
                data Kind = Plain | Express

                data Claim = { kind: Kind, amount: Int }

                data Done = { n: Int }
                data Refused

                behavior settle : (claim: Claim) -> Done | Refused
                    constructs Done

                let settle (claim) = {
                    guard claim.amount > 0 else Refused
                    match claim.kind with
                        | Plain -> Done { n = claim.amount }
                        | Express -> Done { n = claim.amount + 500 }
                }

                let unpaid: Claim = Claim { kind = Plain, amount = 0 }
                """;
        assertEquals("Claim { ...unpaid, kind = Express }",
                rowsOf(stating).get("claim.kind=Express"));
    }

    /**
     * A value the module states for a parameter the row composes is not one the row keeps.
     *
     * <p>The author's row states both parameters, and the row for {@code Meal} is written against
     * it — but its list is composed, since no edit of the stated list makes an element a meal. What
     * stops it at the guard is then a value this compiler chose, and the row is held past it. The
     * row about {@code Express} writes the stated list and keeps it, short of the guard as the
     * author's own row is.
     */
    private static final String STATED_BESIDE_COMPOSED = """
            module example.settle

            data Plain
            data Express
            data Kind = Plain | Express

            data Amount = Int
                invariant value >= 0

            data People = Int
                invariant value >= 1

            data Common = { amount: Amount }
            data Travel = { ...Common }
            data Meal = { ...Common, people: People }
            data Cost = Travel | Meal

            data Item = { cost: Cost }

            data Done = { n: Int }
            data Refused

            behavior settle : (kind: Kind, items: List<Item>) -> Done | Refused
                constructs Done

            let settle (kind, items) = {
                guard List.sum(List.map(i -> i.cost.amount.value, items)) > 0 else Refused
                match kind with
                    | Plain -> Done { n = 1 }
                    | Express -> Done { n = 2 }
            }

            let trip: List<Item> = [Item { cost = Travel { amount = Amount(0) } }]

            example settle
                | "nothing spent" : (Plain, trip) -> Refused
            """;

    @Test
    void aParameterTheRowComposesBesideAStatedValueIsHeldPastTheGuard() {
        Map<String, String> rows = rowsOf(STATED_BESIDE_COMPOSED);
        assertEquals("Plain, [Item { cost = Meal { amount = Amount(1), people = People(1) } }]",
                rows.get("items[*].cost=Meal"));
        assertEquals("Express, trip", rows.get("kind=Express"),
                "the row that writes the stated list keeps it");
    }

    /** A row taken past the guard carries nothing about one. */
    @Test
    void aRowTakenPastTheGuardSaysNothingOfIt() {
        Map<String, RepairShortfall> stops = stopsOf(MODEL);
        assertEquals(List.of(), stops.keySet().stream()
                        .filter(label -> label.startsWith("kind=")).toList(),
                () -> "the rows about the kind went on: " + stops);
    }

    /**
     * The row about the class the guard refuses says why: the one way past it was looked for, and
     * a row in that class going that way is one position standing at two things.
     */
    @Test
    void aRowAboutTheClassTheGuardRefusesSaysWhatTheWayPastCameTo() {
        assertEquals(List.of("searched: ONE_POSITION_CANNOT_BE_BOTH"),
                waysOf(stopsOf(MODEL).get("amount=x <= 0")));
    }

    /**
     * A row kept at a value the module states says the way past would compose that value afresh,
     * and says it was not looked for — not that a search came to nothing.
     */
    @Test
    void aRowKeepingAStatedValueSaysTheWayPastWouldRewriteIt() {
        String stating = MODEL + """

                let noAmount: Int = 0
                """;
        assertEquals(List.of("not searchable: IT_WOULD_REWRITE_A_STATED_VALUE"),
                waysOf(stopsOf(stating).get("kind=Plain")));
    }

    /**
     * Each way in the order the body writes it, whichever was looked for and whichever could not
     * be: a way no border offers a point for is said where it stands, before or after the one that
     * was searched.
     */
    private static final String TWO_WAYS = """
            module example.settle

            data Plain
            data Express
            data Kind = Plain | Express

            data Amount = Int
                invariant value >= 0 && value <= 9

            data Done = { n: Int }
            data Refused

            behavior settle : (kind: Kind, a: Int, b: Amount) -> Done | Refused
                constructs Done

            let settle (kind, a, b) = {
                guard CONDITION else Refused
                match kind with
                    | Plain -> Done { n = 1 }
                    | Express -> Done { n = 2 }
            }
            """;

    @Test
    void eachWayPastIsSaidInTheOrderTheBodyWritesIt() {
        assertEquals(List.of("searched: ONE_POSITION_CANNOT_BE_BOTH",
                        "not searchable: NOTHING_HOLDS_A_ROW_TO_IT"),
                waysOf(stopsOf(TWO_WAYS.replace("CONDITION", "a > 0 || b.value > 20"))
                        .get("a=x <= 0")));
        assertEquals(List.of("not searchable: NOTHING_HOLDS_A_ROW_TO_IT",
                        "searched: ONE_POSITION_CANNOT_BE_BOTH"),
                waysOf(stopsOf(TWO_WAYS.replace("CONDITION", "b.value > 20 || a > 0"))
                        .get("a=x <= 0")));
    }

    /**
     * A guard whose ways past the reading cannot write down is said as that, and never as a guard
     * no row goes past: the first is this compiler's and the second the model's.
     */
    @Test
    void aGuardWhoseWaysPastCannotBeReadSaysSo() {
        // The guard is one rule with a line at each of its relations, so it divides the amount;
        // a class between nought and four is one it refuses, and the way past it is either arm of
        // the choice, which is one of several things and no list of ways.
        RepairShortfall stop = stopsOf(MODEL.replace("guard amount > 0",
                "guard (if amount > 0 then amount else 0 - amount) > 4"))
                .get("amount=0 < x <= 4");
        assertTrue(stop != null && stop.came() instanceof RepairShortfall.AtTheGuard.WaysNotRead,
                () -> "the ways past the guard were not read, which is what is said: " + stop);
    }

    /** A stop says which requirement the looking was done for, which is the class its row is. */
    @Test
    void aStopSaysWhichRequirementItWasLookedFor() {
        RepairShortfall stop = stopsOf(MODEL).get("amount=x <= 0");
        assertNotNull(stop, "the row about the refused class stops at the guard");
        List<String> labels = new ArrayList<>();
        stop.soughtFor().forEach(purpose -> labels.addAll(purpose.labels()));
        assertEquals(List.of("amount=x <= 0"), labels);
    }

    /** What each way past the guard came to, in a word apiece. */
    private static List<String> waysOf(RepairShortfall stop) {
        assertTrue(stop != null && stop.came() instanceof RepairShortfall.AtTheGuard.NoWayPast,
                () -> "the row stops at the guard with every way past it looked at: " + stop);
        List<String> out = new ArrayList<>();
        for (RepairShortfall.WayPast way
                : ((RepairShortfall.AtTheGuard.NoWayPast) stop.came()).ways()) {
            out.add(switch (way) {
                case RepairShortfall.WayPast.Searched(CameToNothing came) ->
                        "searched: " + came.why().reason();
                case RepairShortfall.WayPast.CutShort(CameToNothing came,
                        CompositionBudget figure) ->
                        "cut short at " + figure + ": " + came.why().reason();
                case RepairShortfall.WayPast.NotSearchable(RepairShortfall.Barrier why) ->
                        "not searchable: " + why;
            });
        }
        return out;
    }

    /** Why each row stops where it does, by its label, for the rows that stop at a guard. */
    private static Map<String, RepairShortfall> stopsOf(String source) {
        Map<String, RepairShortfall> out = new LinkedHashMap<>();
        for (FillResult.Offer offer : generated(source).offers()) {
            for (Generator.Purpose purpose : offer.row().purposes()) {
                if (purpose instanceof Generator.Purpose.ForAClass forAClass
                        && offer.stop() != null) {
                    out.put(forAClass.label(), offer.stop());
                }
            }
        }
        return out;
    }

    private static FillResult generated(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, Adequacy.Filling> all = Adequacy.generatedOf(compilation.db(), "example.settle");
        assertNotNull(all, "the model under test compiles");
        return all.get("settle").composed();
    }

    /** What each row is for, by its label, and what it writes. */
    private static Map<String, String> rowsOf(String source) {
        Map<String, String> out = new LinkedHashMap<>();
        for (Generator.GeneratedRow row : generated(source).rows()) {
            String written = String.join(", ", row.inputs().stream().map(i -> i.text()).toList());
            for (Generator.Purpose purpose : row.purposes()) {
                if (purpose instanceof Generator.Purpose.ForAClass forAClass) {
                    out.put(forAClass.label(), written);
                }
            }
        }
        return out;
    }
}
