package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.observe.Limits;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A row is composed past a guard on whether a container holds a value, and a rule on either side of
 * one is offered a row that takes that side.
 *
 * <p>The row for a class the guard is not about is first composed from the classes alone, run,
 * and seen stopping at the guard; what gets it past is the guard coming out the other way, which
 * is a container written holding the value — or kept from it. A rule is composed for on the way
 * to it, and a container a helper answers is the field it answers.
 */
class AGuardOnWhatAContainerHoldsIsComposedPastTest {

    private static final String HOLDING = """
            module example.settle

            data Plain
            data Express
            data Kind = Plain | Express

            data Name = String
                invariant String.length(value) >= 1 && String.length(value) <= 8

            data Lead = { campaigns: Set<Name> }

            data Done = { n: Int }
            data Refused

            behavior settle : (kind: Kind, lead: Lead, priority: Name) -> Done | Refused
                constructs Done

            let settle (kind, lead, priority) = {
                guard Set.contains(priority, lead.campaigns) else Refused
                match kind with
                    | Plain -> Done { n = 1 }
                    | Express -> Done { n = 2 }
            }
            """;

    /** The campaigns hold one at the fewest, so a row composed from the classes alone holds the
     *  very value the guard keeps out. */
    private static final String KEPT_OUT = """
            module example.settle

            data Plain
            data Express
            data Kind = Plain | Express

            data Name = String
                invariant String.length(value) >= 1 && String.length(value) <= 8

            data Lead = { campaigns: Set<Name> }
                invariant Set.size(campaigns) >= 1

            data Done = { n: Int }
            data Refused

            behavior settle : (kind: Kind, lead: Lead, priority: Name) -> Done | Refused
                constructs Done

            let settle (kind, lead, priority) = {
                guard Bool.not(Set.contains(priority, lead.campaigns)) else Refused
                match kind with
                    | Plain -> Done { n = 1 }
                    | Express -> Done { n = 2 }
            }
            """;

    /** The value the set is to hold is a field of a parameter the model states a value of, which
     *  a row is written against. */
    private static final String READ_OFF_A_STATED_VALUE = """
            module example.settle

            data Plain
            data Express
            data Kind = Plain | Express

            data Request = { level: Int, note: Int }

            data Other = { allowed: Set<Int> }

            data Done = { n: Int }
            data Refused

            let usual = Request { level = 1, note = 1 }

            behavior settle : (kind: Kind, other: Other, request: Request) -> Done | Refused
                constructs Done

            let settle (kind, other, request) = {
                guard Set.contains(request.level, other.allowed) else Refused
                if request.level > 5 then Done { n = 1 }
                else match kind with
                    | Plain -> Done { n = 2 }
                    | Express -> Done { n = 3 }
            }
            """;

    /** The same, with nothing in the body dividing the field, so no row moves it. */
    private static final String ONLY_NAMED = """
            module example.settle

            data Plain
            data Express
            data Kind = Plain | Express

            data Request = { level: Int, note: Int }

            data Other = { allowed: Set<Int> }

            data Done = { n: Int }
            data Refused

            let usual = Request { level = 1, note = 1 }

            behavior settle : (kind: Kind, other: Other, request: Request) -> Done | Refused
                constructs Done

            let settle (kind, other, request) = {
                guard Set.contains(request.level, other.allowed) else Refused
                match kind with
                    | Plain -> Done { n = 2 }
                    | Express -> Done { n = 3 }
            }
            """;

    private static final String SCORED = """
            module example.settle

            data Name = String
                invariant String.length(value) >= 1 && String.length(value) <= 8

            data Lead = { campaigns: Set<Name> }

            data Score = { points: Int }

            let campaignsOf (lead: Lead): Set<Name> = lead.campaigns

            behavior settle : (lead: Lead, priority: Name) -> Score

            let settle (lead, priority) =
                Score { points = if Set.contains(priority, campaignsOf(lead)) then 25 else 0 }
            """;

    /** The rows about {@code kind} are past the guard: the campaigns hold the priority. */
    @Test
    void aRowAboutAnotherPositionGoesOnPastTheGuard() {
        for (String kind : List.of("kind=Plain", "kind=Express")) {
            List<String> row = generatedOf(HOLDING).classes().get(kind);
            assertNotNull(row, () -> "a row is offered for " + kind);
            assertTrue(holds(row.get(1), row.get(2)), () -> "the row holds the priority: " + row);
        }
    }

    /** And past a guard on its not holding it: the campaigns are kept from the priority. */
    @Test
    void aRowAboutAnotherPositionGoesOnPastAGuardThatKeepsTheValueOut() {
        for (String kind : List.of("kind=Plain", "kind=Express")) {
            List<String> row = generatedOf(KEPT_OUT).classes().get(kind);
            assertNotNull(row, () -> "a row is offered for " + kind);
            assertFalse(holds(row.get(1), row.get(2)),
                    () -> "the row keeps the priority out: " + row);
        }
    }

    /**
     * A container handed a field of a parameter written against a value the model states holds
     * what the row writes at that field.
     */
    @Test
    void aFieldTheRowMovesOffAStatedValueIsHeld() {
        Rows rows = generatedOf(READ_OFF_A_STATED_VALUE);
        int moved = 0;
        for (List<String> each : rows.classes().values()) {
            Matcher level = Pattern.compile("\\.\\.\\.usual, level = (-?\\d+)").matcher(each.get(2));
            if (level.find()) {
                moved++;
                assertTrue(each.get(1).matches(".*allowed = \\[[^]]*\\b" + level.group(1) + "\\b.*"),
                        () -> "the set holds the level the row writes: " + each);
            }
        }
        assertTrue(moved > 0, () -> "some row moves the level off the stated value: " + rows);
    }

    /**
     * A container handed a field of a stated value the row names without moving it holds what the
     * boundary built there, and the row goes on naming the value.
     *
     * <p>Both halves. The request is still the author's value, written by its name rather than
     * composed afresh or spelled out; and the set holds the level that value has, which nothing in
     * the row writes — so the row is past the guard and nothing is said of it stopping there.
     */
    @Test
    void aFieldOnlyNamedIsHandedOnAsTheBoundaryBuiltIt() {
        Rows rows = generatedOf(ONLY_NAMED);
        List<String> row = rows.classes().get("kind=Plain");
        assertNotNull(row, () -> "a row is offered for the kind: " + rows);
        assertEquals("usual", row.get(2),
                () -> "the request is the stated value, not composed afresh: " + row);
        assertEquals(List.of("1"), elementsOf(row.get(1), "allowed"),
                () -> "the set holds the level the stated value has: " + row);
        assertNull(rows.stops().get("kind=Plain"),
                () -> "and the row is past the guard: " + rows.stops());
    }

    /**
     * Where what was built at the field is nothing this can write — a string longer than an
     * observation reads — the row still names the stated value and stops at the guard, and the
     * way past it came to this compiler composing nothing: never the model refusing a value, and
     * never the rules leaving nothing there.
     */
    @Test
    void aFieldBuiltAsNothingThisCanWriteIsSaidAsNothingComposingOne() {
        Rows rows = generatedOf(ONLY_NAMED
                .replace("level: Int", "level: String")
                .replace("Set<Int>", "Set<String>")
                .replace("level = 1", "level = \"" + "x".repeat(Limits.DEFAULT.maxText() + 1)
                        + "\""));
        assertEquals("usual", rows.classes().get("kind=Plain").get(2),
                () -> "the request is the stated value, not composed afresh: " + rows);
        RepairShortfall stop = rows.stops().get("kind=Plain");
        assertTrue(stop != null && stop.came() instanceof RepairShortfall.AtTheGuard.NoWayPast,
                () -> "the row stops at the guard with every way past it looked at: " + stop);
        List<Generator.UnresolvedCombination.Reason> said = new ArrayList<>();
        for (RepairShortfall.WayPast way
                : ((RepairShortfall.AtTheGuard.NoWayPast) stop.came()).ways()) {
            assertTrue(way instanceof RepairShortfall.WayPast.Searched,
                    () -> "each way was looked for to the end: " + way);
            said.add(((RepairShortfall.WayPast.Searched) way).came().why().reason());
        }
        assertEquals(List.of(Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE), said,
                () -> "the way past the guard came to this compiler composing nothing: " + stop);
    }

    /** The field composed rather than stated, at a type whose strings are longer than an
     *  observation reads. */
    private static final String COMPOSED_PAST_WHAT_IS_OBSERVED = """
            module example.settle

            data Plain
            data Express
            data Kind = Plain | Express

            data Long = String
                invariant String.length(value) >= %d

            data Request = { level: Long, note: Int }

            data Other = { allowed: Set<Long> }

            data Done = { n: Int }
            data Refused

            behavior settle : (kind: Kind, other: Other, request: Request) -> Done | Refused
                constructs Done

            let settle (kind, other, request) = {
                guard Set.contains(request.level, other.allowed) else Refused
                match kind with
                    | Plain -> Done { n = 2 }
                    | Express -> Done { n = 3 }
            }
            """.formatted(Limits.DEFAULT.maxText() + 1);

    /**
     * And the same of a value composed here: every value built had nothing to hand on, which is
     * this compiler composing nothing and not every candidate refused by the model.
     */
    @Test
    void aComposedFieldBuiltAsNothingThisCanWriteIsSaidAsNothingComposingOne() {
        Rows rows = generatedOf(COMPOSED_PAST_WHAT_IS_OBSERVED);
        RepairShortfall stop = rows.stops().get("kind=Plain");
        assertTrue(stop != null && stop.came() instanceof RepairShortfall.AtTheGuard.NoWayPast,
                () -> "the row stops at the guard with every way past it looked at: " + rows);
        List<Generator.UnresolvedCombination.Reason> said = new ArrayList<>();
        for (RepairShortfall.WayPast way
                : ((RepairShortfall.AtTheGuard.NoWayPast) stop.came()).ways()) {
            assertTrue(way instanceof RepairShortfall.WayPast.Searched,
                    () -> "each way was looked for to the end: " + way);
            said.add(((RepairShortfall.WayPast.Searched) way).came().why().reason());
        }
        assertEquals(List.of(Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE), said,
                () -> "the way past the guard came to this compiler composing nothing: " + stop);
    }

    /** The elements written in the collection at {@code field} of a record written as {@code
     *  record}. */
    private static List<String> elementsOf(String record, String field) {
        Matcher found = Pattern.compile(field + " = \\[([^]]*)]").matcher(record);
        assertTrue(found.find(), () -> field + " is written in " + record);
        String inside = found.group(1).trim();
        return inside.isEmpty() ? List.of()
                : Arrays.stream(inside.split(",")).map(String::trim).toList();
    }

    /**
     * The same where the lead is one of two cases, both of which have the campaigns: the set is a
     * name every case spreads, and the row is written as one of the cases holding it there.
     */
    private static final String SCORED_OVER_A_SUM = """
            module example.settle

            data Name = String
                invariant String.length(value) >= 1 && String.length(value) <= 8

            data LeadCommon = { campaigns: Set<Name> }
            data NewLead = { ...LeadCommon, fresh: Bool }
            data WorkingLead = { ...LeadCommon, touches: Int }
            data OpenLead = NewLead | WorkingLead

            data Score = { points: Int }

            let campaignsOf (lead: OpenLead): Set<Name> = lead.campaigns

            behavior settle : (lead: OpenLead, priority: Name) -> Score

            let settle (lead, priority) =
                Score { points = if Set.contains(priority, campaignsOf(lead)) then 25 else 0 }
            """;

    /** And where the container is a name every case of a sum spreads. */
    @Test
    void eachSideIsOfferedARowWhereTheContainerIsSpreadByTheCases() {
        Rows rows = generatedOf(SCORED_OVER_A_SUM);
        assertEquals(2, rows.rules().size(), () -> "a row for each side: " + rows);
        for (Map.Entry<Boolean, List<String>> each : rows.rules().entrySet()) {
            List<String> row = each.getValue();
            assertEquals(each.getKey(), holds(row.get(0), row.get(1)),
                    () -> "the row for the side coming out " + each.getKey() + ": " + row);
        }
    }

    /** A guard on an operation's truth that asks two things of a row at once. */
    private static final String TWO_THINGS_AT_ONCE = """
            module example.settle

            data Plain
            data Express
            data Kind = Plain | Express

            data Item = { n: Int }
                invariant n >= 0 && n <= 9

            data Order = { items: List<Item>, gate: Int }
                invariant gate >= -5 && gate <= 5

            data Done = { n: Int }
            data Refused

            behavior settle : (kind: Kind, order: Order) -> Done | Refused
                constructs Done

            let settle (kind, order) = {
                guard List.any(i -> i.n > 5 && order.gate > 0, order.items) else Refused
                match kind with
                    | Plain -> Done { n = 1 }
                    | Express -> Done { n = 2 }
            }
            """;

    /**
     * Some element meeting what the predicate asks of it, and what the predicate asks of the rest
     * of the row beside it, are one truth coming out — so a row is held to both, rather than to
     * neither for there being two.
     */
    @Test
    void aTruthAskingTwoThingsAtOnceHoldsTheRowToBoth() {
        Rows rows = generatedOf(TWO_THINGS_AT_ONCE);
        for (String kind : List.of("kind=Plain", "kind=Express")) {
            List<String> row = rows.classes().get(kind);
            assertNotNull(row, () -> "a row is offered for " + kind + ": " + rows);
            Matcher gate = Pattern.compile("gate = (-?\\d+)").matcher(row.get(1));
            assertTrue(gate.find() && Integer.parseInt(gate.group(1)) > 0,
                    () -> "the gate is past the guard: " + row);
            Matcher n = Pattern.compile("n = (\\d+)").matcher(row.get(1));
            boolean some = false;
            while (n.find()) {
                some |= Integer.parseInt(n.group(1)) > 5;
            }
            assertTrue(some, () -> "and some item is: " + row);
        }
    }

    /** A rule on each side of the membership is offered a row on that side. */
    @Test
    void eachSideOfTheMembershipIsOfferedARowThatTakesIt() {
        Rows rows = generatedOf(SCORED);
        assertEquals(2, rows.rules().size(), () -> "a row for each side: " + rows.rules());
        for (Map.Entry<Boolean, List<String>> each : rows.rules().entrySet()) {
            List<String> row = each.getValue();
            assertEquals(each.getKey(), holds(row.get(0), row.get(1)),
                    () -> "the row for the side coming out " + each.getKey() + ": " + row);
        }
    }

    /** What one module's behavior was offered: a row per class, one per side of the membership a
     *  rule turns on, and why each class's row stops where it does where it stops at a guard. */
    private record Rows(Map<String, List<String>> classes, Map<Boolean, List<String>> rules,
                        Map<String, RepairShortfall> stops) {}

    /** What each model was offered, compiled once however many tests ask about it. */
    private static final Map<String, Rows> GENERATED = new ConcurrentHashMap<>();

    private static Rows generatedOf(String source) {
        return GENERATED.computeIfAbsent(source,
                AGuardOnWhatAContainerHoldsIsComposedPastTest::generated);
    }

    private static Rows generated(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, Adequacy.Filling> all =
                Adequacy.generatedOf(compilation.db(), "example.settle");
        assertNotNull(all, "the model under test compiles");
        Adequacy.Filling filling = all.get("settle");
        Map<String, List<String>> classes = new LinkedHashMap<>();
        Map<String, RepairShortfall> stops = new LinkedHashMap<>();
        for (FillResult.Offer offer : filling.composed().offers()) {
            for (Generator.Purpose purpose : offer.row().purposes()) {
                if (purpose instanceof Generator.Purpose.ForAClass forAClass) {
                    classes.put(forAClass.label(), written(offer.row()));
                    if (offer.stop() != null) {
                        stops.put(forAClass.label(), offer.stop());
                    }
                }
            }
        }
        Map<Boolean, List<String>> rules = new LinkedHashMap<>();
        filling.rules().byRule().forEach((rule, row) -> rule.consulted().values().stream()
                .filter(each -> each instanceof DecidedCondition.Unread)
                .forEach(each -> rules.put(((DecidedCondition.Unread) each).held(),
                        written(row))));
        return new Rows(classes, rules, stops);
    }

    private static List<String> written(Generator.GeneratedRow row) {
        return new ArrayList<>(row.inputs().stream().map(FixtureTemplate::text).toList());
    }

    /** Whether the campaigns written in {@code lead} hold {@code value}. */
    private static boolean holds(String lead, String value) {
        Matcher found = Pattern.compile("campaigns = \\[([^]]*)]").matcher(lead);
        assertTrue(found.find(), () -> "the campaigns are written in " + lead);
        String inside = found.group(1).trim();
        return !inside.isEmpty() && Arrays.stream(inside.split(",")).map(String::trim)
                .anyMatch(value::equals);
    }
}
