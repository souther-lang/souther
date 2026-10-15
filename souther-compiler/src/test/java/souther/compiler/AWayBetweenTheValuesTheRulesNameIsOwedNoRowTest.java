package souther.compiler;

import org.junit.jupiter.api.Test;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;
import souther.compiler.check.PathReachability;
import souther.compiler.coverage.ControlPlace;
import souther.compiler.coverage.SeenConditionOutcome;
import souther.compiler.diag.SourceRendering;
import souther.compiler.partition.DecisionRule;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.RuleRequirement;
import souther.compiler.query.RuleSearch;
import souther.compiler.query.SettledAcross;
import souther.compiler.query.SettledAt;
import souther.compiler.reach.Reachability;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
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
 * what says so is the reading of the body's reach, the one the branch count is made by, and not a
 * search that came to nothing. Both measures read that one answer: the arm leaves the branch count,
 * and the rule of the decision through it is out by the comparison it needs to come out a way
 * nothing arrives at coming out so.
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

        assertEquals(List.of("a_comparison_outcome_nothing_reaches"), excludedBecause(model),
                "the rule through the inner `then` is the one out, and by the reading of reach");
        String page = human(model);
        assertTrue(page.contains("branch      3/3"),
                () -> "the inner `then` leaves the branch count:\n" + page);
        assertFalse(page.contains("no row goes through"), () -> page);
        assertFalse(page.contains("no row expects `Low`"),
                () -> "and `Low`, which only that arm answers, is owed no row either:\n" + page);
    }

    @Test
    void aWayBetweenTheStringsIsOutTheSameWay() {
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

        assertEquals(List.of("a_comparison_outcome_nothing_reaches"), excludedBecause(model));
        String page = human(model);
        assertTrue(page.contains("branch      5/5"), () -> page);
        assertFalse(page.contains("no row expects `Low`"), () -> page);
    }

    /** The control: one value of the three lies under the bound. Without it the two above would
     *  hold of a measure that had stopped owing the inner `then` anything at all. */
    @Test
    void aWayOneOfTheValuesTakesIsOwedARow() {
        String model = ODD.replace("BOUND", "4");

        assertEquals(List.of(), excludedBecause(model), "3 takes the way through the inner `then`");
        String page = human(model);
        assertTrue(page.contains("no row goes through `then`"),
                () -> "and nothing went through it:\n" + page);
    }

    /**
     * The settlement was the model's, read off the rules before anything was composed.
     *
     * <p>Which is what keeps the word from being a search's: a search that came to nothing says
     * {@link RuleRequirement.Excluded.NoValueCanTakeIt}, and this one composed no row at all.
     */
    @Test
    void nothingIsComposedForTheRule() {
        List<SettledAt> out = excludedPlaces(ODD.replace("BOUND", "3"));

        assertEquals(1, out.size(), () -> "one rule, stated at one place: " + out);
        assertInstanceOf(RuleRequirement.Excluded.AComparisonOutcomeNothingReaches.class,
                out.getFirst().settlement().requirement());
        assertInstanceOf(RuleSearch.NotMade.class, out.getFirst().settlement().search());
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
     * fork beside one way through the second's: three by three. The ways through the middle of the
     * first call are out, since what it is handed is one of the three. Those through the middle of
     * the second are out only where the second is handed one of the three as well — a 2 handed in
     * there takes them, and a copy of the first speaking for the second would take them away.
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
        // By the reading of reach and not by a search: a search finds the same ways empty where it
        // composes a row for each, and counted without the word this would hold of a compiler that
        // had stopped reading what a call's copy is handed.
        assertEquals(List.of("a_comparison_outcome_nothing_reaches",
                        "a_comparison_outcome_nothing_reaches",
                        "a_comparison_outcome_nothing_reaches"),
                excludedBecause(twoCalls("e")),
                "the three ways through the first call's middle, and none through the second's");
        assertEquals(5, excludedBecause(twoCalls("d.value")).stream()
                        .filter("a_comparison_outcome_nothing_reaches"::equals).count(),
                "the three through either call's middle, the one through both counted once");
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

    /** Every place of every rule the decision search settled as excluded. */
    private static List<SettledAt> excludedPlaces(String model) {
        Compilation compilation = measured(model);
        Map<DecisionRule, SettledAcross> rules = compilation.db()
                .ask(new Adequacy.DecisionSearch(compilation.modules().getFirst(), "pick"))
                .value();
        List<SettledAt> out = new ArrayList<>();
        rules.values().forEach(settled -> settled.places().stream()
                .filter(place -> place.settlement().requirement()
                        instanceof RuleRequirement.Excluded)
                .forEach(out::add));
        return out;
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
