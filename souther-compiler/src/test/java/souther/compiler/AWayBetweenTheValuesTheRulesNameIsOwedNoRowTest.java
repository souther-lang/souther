package souther.compiler;

import org.junit.jupiter.api.Test;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;
import souther.compiler.check.PathReachability;
import souther.compiler.coverage.ControlPlace;
import souther.compiler.coverage.SeenConditionOutcome;
import souther.compiler.diag.SourceRendering;
import souther.compiler.partition.DecisionReading;
import souther.compiler.partition.DecisionRule;
import souther.compiler.partition.NoInputTakesIt;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.RuleRequirement;
import souther.compiler.query.SettledAcross;
import souther.compiler.reach.Reachability;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A way written between the values a position's rules name is one no row takes.
 *
 * <p>{@code Odd} holds 1, 3 and 7. A way that needs its value at or above 2 and below 3 asks for a
 * value inside the range the three run between and outside the three, so nothing takes it — and
 * what says so is a proof had of the model, and not a search that came to nothing. The reading of
 * the body's reach, the one the branch count is made by, takes the arm out of the branch count. The
 * reading of the decision proves the way through it one no input takes, by the numbers its two
 * comparisons state with what {@code Odd} holds, and holds that way once in place of the rules past
 * it.
 *
 * <p>Between strings, whose order has no arithmetic to say a range in, the numbers prove nothing:
 * the rule is read as any other, and it is the reading of reach that puts it out, by the comparison
 * it needs to come out a way nothing arrives at coming out so.
 */
class AWayBetweenTheValuesTheRulesNameIsOwedNoRowTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String ODD = """
            module example.odd

            data Low
            data High
            data Odd = Int
                invariant value == 1 || value == 3 || value == 7

            behavior pick : (c: Odd) -> Low | High
            let pick (c) = if c.value < 2 then High else if c.value < BOUND then Low else High

            example pick
              | "one" : (Odd(1)) -> High
              | "seven" : (Odd(7)) -> High
            """;

    /** The same between strings, whose order has no arithmetic to say a range in. */
    private static final String CODE = """
            module example.code

            data Low
            data High
            data Code = String
                invariant value == "a" || value == "c" || value == "e"

            behavior pick : (c: Code) -> Low | High
            let pick (c) = if c.value < "b" then High else if c.value < "c" then Low else High

            example pick
              | "a" : (Code("a")) -> High
              | "c" : (Code("c")) -> High
              | "e" : (Code("e")) -> High
            """;

    @Test
    void aWayBetweenTheNumbersIsOutByTheComparisonItNeeds() {
        String model = ODD.replace("BOUND", "3");

        assertEquals(List.of("the_numbers_on_the_way_leave_none"), waysNoInputTakes(model),
                "the way through the inner `then` is the one no input takes, and by the numbers");
        assertEquals(List.of(), excludedBecause(model),
                "and no rule past it is an obligation to be put out");
        DecisionReading read = reading(model);
        DecisionReading.ImpossiblePath way = read.impossible().getFirst();
        assertEquals(2, way.way().rule().consulted().size(),
                () -> "the way is the two comparisons the inner `then` needs: " + way);
        assertEquals(2, read.rules().size(),
                () -> "the rules left are the outer `then` and the inner `else`: " + read.found());
        assertTrue(read.rules().stream().noneMatch(way::standsFor),
                () -> "and neither is past the way: " + read.found());
        String page = human(model);
        assertTrue(saysTheWays(page, List.of(
                        "      · no input takes 1 way through this body, and no row is owed at a"
                                + " rule past it",
                        "          · the declarations and the conditions on the way leave no value:",
                        "              · the comparison at 9:27 does not hold",
                        "              · the comparison at 9:57 holds")),
                () -> "the page says the way by the two comparisons:\n" + page);
        assertTrue(page.contains("decision    rules 2"),
                () -> "and counts it apart from the rules:\n" + page);
        assertTrue(page.contains("branch      3/3"),
                () -> "the inner `then` leaves the branch count:\n" + page);
        assertFalse(page.contains("no row goes through"), () -> page);
        assertFalse(page.contains("no row expects `Low`"),
                () -> "and `Low`, which only that arm answers, is owed no row either:\n" + page);
    }

    @Test
    void aWayBetweenTheStringsIsOutByTheReadingOfReach() {
        assertEquals(List.of(), waysNoInputTakes(CODE), "no numbers say the gap between strings");
        assertEquals(List.of("a_comparison_outcome_nothing_reaches"), excludedBecause(CODE));
        String page = human(CODE);
        assertTrue(page.contains("branch      3/3"), () -> page);
    }

    /**
     * The same of a value an arm binds, which is no position of the input.
     *
     * <p>What a declaration leaves a value holds wherever a value of it is named — a parameter, what
     * a {@code match} arm binds, what a call answers — so the gap is one nothing enters whichever
     * of them the condition is written on.
     */
    @Test
    void aWayBetweenTheValuesOfAValueAnArmBindsIsOutTheSameWay() {
        String model = """
                module example.bound

                data Low
                data High
                data Odd = Int
                    invariant value == 1 || value == 3 || value == 7
                data Blank
                data Choice = Odd | Blank

                behavior pick : (p: Choice) -> Low | High
                let pick (p) = match p with
                    | Odd as o -> if o.value < 2 then High else if o.value < 3 then Low else High
                    | Blank -> High

                example pick
                    | "one" : (Odd(1)) -> High
                    | "three" : (Odd(3)) -> High
                    | "seven" : (Odd(7)) -> High
                    | "blank" : (Blank) -> High
                """;

        assertEquals(List.of("the_numbers_on_the_way_leave_none"), waysNoInputTakes(model));
        assertEquals(List.of(), excludedBecause(model));
        String page = human(model);
        assertTrue(saysTheWays(page, List.of(
                        "          · the declarations and the conditions on the way leave no value:",
                        "              · the comparison at 12:30 does not hold",
                        "              · the comparison at 12:60 holds")),
                () -> "the way is the two comparisons of what the arm binds, and nothing of the"
                        + " arm it takes them under:\n" + page);
        assertTrue(page.contains("branch      5/5"), () -> page);
        assertFalse(page.contains("no row expects `Low`"), () -> page);
    }

    /** The control: one value of the three lies under the bound. Without it the two above would
     *  hold of a measure that had stopped owing the inner `then` anything at all. */
    @Test
    void aWayOneOfTheValuesTakesIsOwedARow() {
        String model = ODD.replace("BOUND", "4");

        assertEquals(List.of(), excludedBecause(model), "3 takes the way through the inner `then`");
        assertEquals(List.of(), waysNoInputTakes(model), "so nothing proves no input takes it");
        String page = human(model);
        assertTrue(page.contains("no row goes through `then`"),
                () -> "and nothing went through it:\n" + page);
    }

    /**
     * The proof was the model's, had where the ways were read, before anything was composed.
     *
     * <p>Which is what keeps it from being a search's: a search that came to nothing says
     * {@link RuleRequirement.Excluded.NoValueCanTakeIt}, and this one was handed no rule past the
     * way at all.
     */
    @Test
    void nothingIsComposedForTheRule() {
        String model = ODD.replace("BOUND", "3");
        DecisionReading.ImpossiblePath way = reading(model).impossible().getFirst();

        assertInstanceOf(NoInputTakesIt.TheNumbersLeaveNone.class, way.why());
        assertEquals(Map.of(), searched(model),
                "the two rules left are taken by the rows, and nothing past the way is a rule to"
                        + " hand the search");
        assertTrue(reading(model).rules().stream().noneMatch(way::standsFor),
                () -> "the rules are the two left: " + reading(model).found());
    }

    /**
     * A way past a comparison inside {@code &&}.
     *
     * <p>The arm the condition fails into is reached by a {@code c} that made the right side false
     * and by one that never ran it, so what is out here is the way the right side comes out true
     * after the left did — and the `else`, which 1 reaches without the right side running, stays.
     */
    @Test
    void aComparisonInsideAConjunctionIsOutAsTheComparisonAndNotAsTheArm() {
        String model = """
                module example.both

                data Low
                data High
                data Odd = Int
                    invariant value == 1 || value == 3 || value == 7

                behavior pick : (c: Odd) -> Low | High
                let pick (c) = if c.value >= 2 && c.value < 3 then Low else High

                example pick
                  | "one" : (Odd(1)) -> High
                  | "three" : (Odd(3)) -> High
                """;

        assertEquals(List.of("a_comparison_outcome_nothing_reaches"), excludedBecause(model),
                "the one rule out is the one needing both sides true");
        String page = human(model);
        assertTrue(page.contains("branch      1/1"),
                () -> "the `then` leaves the count and the `else` stays in it:\n" + page);
    }

    /**
     * A helper's comparison stands once per call, and each call's copy is out on its own reading.
     *
     * <p>{@code pick} decides by both calls, so a rule of it is one way through the first call's
     * fork beside one way through the second's: three by three. The way through the middle of the
     * first call is one no input takes, since what it is handed is one of the three, and it stands
     * for the three rules past it. The way through the middle of the second is one only where the
     * second is handed one of the three as well — a 2 handed in there takes it, and a copy of the
     * first's proof speaking for the second would take its rules away.
     *
     * @param second what the second call hands the helper: a value of {@code Odd} again, or a
     *               number nothing holds to the three
     */
    private static String twoCalls(String second) {
        return """
                module example.band

                data Odd = Int
                    invariant value == 1 || value == 3 || value == 7
                data Answer = Int

                let band (n: Int): Answer =
                    if n < 2 then Answer(1) else if n < 3 then Answer(2) else Answer(1)

                behavior pick : (c: Odd, d: Odd, e: Int) -> Answer
                    constructs Answer
                let pick (c, d, e) = Answer(band(c.value).value + band(SECOND).value)

                example pick
                  | "one" : (Odd(1), Odd(1), 1) -> Answer(2)
                """.replace("SECOND", second);
    }

    @Test
    void aHelpersComparisonIsOutAtACallOnlyByWhatThatCallHandsIt() {
        // By a proof had where the ways are read and not by a search: a search finds the same ways
        // empty where it composes a row for each, and counted without the proof this would hold of
        // a compiler that had stopped reading what a call's copy is handed.
        String handedAnyNumber = human(twoCalls("e"));
        assertEquals(List.of("the_numbers_on_the_way_leave_none"), waysNoInputTakes(twoCalls("e")),
                "one way, through the first call's middle");
        assertTrue(saysTheWays(handedAnyNumber, List.of(
                        "      · no input takes 1 way through this body, and no row is owed at a"
                                + " rule past it",
                        "          · the declarations and the conditions on the way leave no value:",
                        "              · the comparison at 8:10 does not hold in band@12:29",
                        "              · the comparison at 8:39 holds in band@12:29")),
                () -> "the way is at the first call:\n" + handedAnyNumber);
        assertTrue(handedAnyNumber.contains("decision    rules 6"),
                () -> "the three past it are no rules:\n" + handedAnyNumber);
        assertEquals(List.of(), excludedBecause(twoCalls("e")));
        assertEquals(2, rulesNoRowTakesThrough(handedAnyNumber,
                        "the comparison at 8:10 does not hold in band@12:51",
                        "the comparison at 8:39 holds in band@12:51"),
                () -> "and the two through the second call's middle are owed:\n" + handedAnyNumber);

        String handedAnOdd = human(twoCalls("d.value"));
        assertEquals(List.of("the_numbers_on_the_way_leave_none",
                        "the_numbers_on_the_way_leave_none"),
                waysNoInputTakes(twoCalls("d.value")), "a way through either call's middle");
        assertTrue(saysTheWays(handedAnOdd, List.of(
                        "      · no input takes 2 ways through this body, and no row is owed at a"
                                + " rule past them",
                        "          · the declarations and the conditions on the way leave no value:",
                        "              · the comparison at 8:10 does not hold in band@12:29",
                        "              · the comparison at 8:39 holds in band@12:29",
                        "          · the declarations and the conditions on the way leave no value:",
                        "              · the comparison at 8:10 does not hold in band@12:51",
                        "              · the comparison at 8:39 holds in band@12:51")),
                () -> "each at its own call:\n" + handedAnOdd);
        assertTrue(handedAnOdd.contains("decision    rules 4"),
                () -> "the five past either are no rules, the one past both counted once:\n"
                        + handedAnOdd);
    }

    /**
     * A row seen bringing a comparison out a way this reading had proven nothing arrives at shows
     * the proof wrong, and the answers every measure reads are the corrected ones.
     */
    @Test
    void aRowThatBroughtTheComparisonOutThatWayTakesTheProofBack() {
        Compilation compilation = measured(ODD.replace("BOUND", "3"));
        PathReachability.Answers proven = compilation.db()
                .ask(new Adequacy.PathReached(compilation.modules().getFirst())).value()
                .get("pick");
        List<ControlPlace.Outcome> out = new ArrayList<>();
        proven.found().forEach((place, said) -> {
            if (place instanceof ControlPlace.Outcome outcome
                    && said instanceof Reachability.Unreachable) {
                out.add(outcome);
            }
        });
        assertEquals(1, out.size(), () -> "the inner comparison coming out true: " + out);
        ControlPlace.Outcome proof = out.getFirst();

        assertInstanceOf(Reachability.Unreachable.class,
                proven.asRunWith(Set.of(), Set.of()).answers().at(proof),
                "no row saw it, so the proof stands");
        assertInstanceOf(Reachability.Unreachable.class,
                proven.asRunWith(Set.of(), Set.of(new SeenConditionOutcome(proof.at(),
                        !proof.held()))).answers().at(proof),
                "a row seeing it come out the other way says nothing against it");
        assertEquals(Set.of(), proven.asRunWith(Set.of(), Set.of(new SeenConditionOutcome(
                        proof.at(), !proof.held()))).contradicted().places(),
                "and nothing it says is shown wrong");
        PathReachability.Answers.AsRun ran = proven.asRunWith(Set.of(),
                Set.of(new SeenConditionOutcome(proof.at(), proof.held())));
        assertInstanceOf(Reachability.Reachable.class, ran.answers().at(proof),
                "a row seeing it come out that way takes the proof back");
        assertEquals(Set.of(proof), ran.contradicted().places(),
                "and the reading keeps which proof that was, as it does for an arm");
    }

    /** The words the decision's excluded rules were settled by, one per rule. */
    private static List<String> excludedBecause(String model) {
        JsonNode rules = JSON.readTree(json(model))
                .get("modules").get(0).get("behaviors").get(0)
                .get("decision").get("obligations");
        List<String> out = new ArrayList<>();
        rules.forEach(rule -> {
            if (rule.get("requirement") != null
                    && "excluded".equals(rule.get("requirement").stringValue())) {
                out.add(rule.get("because").get(0).stringValue());
            }
        });
        return out;
    }

    /** The words the decision's ways no input takes were proved by, one per way. */
    private static List<String> waysNoInputTakes(String model) {
        JsonNode ways = JSON.readTree(json(model))
                .get("modules").get(0).get("behaviors").get(0)
                .get("decision").get("waysNoInputTakes");
        List<String> out = new ArrayList<>();
        if (ways != null) {
            ways.forEach(way -> out.add(way.get("because").stringValue()));
        }
        return out;
    }

    /** The reading of {@code pick}'s decision. */
    private static DecisionReading reading(String model) {
        Compilation compilation = measured(model);
        return compilation.db()
                .ask(new Adequacy.DecisionReadings(compilation.modules().getFirst())).value()
                .get("pick");
    }

    /** Every rule the decision search was handed, with what it settled. */
    private static Map<DecisionRule, SettledAcross> searched(String model) {
        Compilation compilation = measured(model);
        return compilation.db()
                .ask(new Adequacy.DecisionSearch(compilation.modules().getFirst(), "pick"))
                .value();
    }

    /** Whether {@code page} says {@code lines}, one after another. */
    private static boolean saysTheWays(String page, List<String> lines) {
        return Collections.indexOfSubList(page.lines().toList(), lines) >= 0;
    }

    /** How many rules the page says no row takes whose conditions include every one of
     *  {@code conditions}. */
    private static long rulesNoRowTakesThrough(String page, String... conditions) {
        List<List<String>> rules = new ArrayList<>();
        List<String> current = null;
        for (String line : page.lines().toList()) {
            if (line.equals("      ! no row takes a decision rule")) {
                current = new ArrayList<>();
                rules.add(current);
            } else if (current != null && line.startsWith("          · ")) {
                current.add(line.substring("          · ".length()));
            } else {
                current = null;
            }
        }
        return rules.stream().filter(rule -> rule.containsAll(List.of(conditions))).count();
    }

    private static String human(String model) {
        Compilation compilation = measured(model);
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static String json(String model) {
        Compilation compilation = measured(model);
        return AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts()));
    }

    /** Each model measured once for the class: several tests read the numeric model, and a test
     *  reads both reports of one. */
    private static final Map<String, Compilation> MEASURED = new ConcurrentHashMap<>();

    private static Compilation measured(String model) {
        return MEASURED.computeIfAbsent(model,
                AWayBetweenTheValuesTheRulesNameIsOwedNoRowTest::measure);
    }

    private static Compilation measure(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(e -> e.diagnostic().code().toString()).toList(),
                "the model under test compiles");
        return compilation;
    }
}
