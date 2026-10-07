package souther.compiler.inputs;

import org.junit.jupiter.api.Test;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.core.Core;
import souther.compiler.partition.DecidedCondition;
import souther.compiler.partition.DecisionReading;
import souther.compiler.partition.DecisionRule;
import souther.compiler.partition.DecisionSubject;
import souther.compiler.partition.OnTheWay;
import souther.compiler.partition.TakenConstraint;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.DecisionEvidence;

import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An arm naming a case that is itself a sum narrows the position to the leaves under it that the
 * declaration leaves, and the arms inside it narrow that narrowing.
 *
 * <p>{@code OnceKind} over a field declared {@code VisitKind} leaves the field {@code Station} or
 * {@code Hospital}. That is a narrowing of the field like any other — it is just not one leaf — so
 * the name the arm binds stands at the field narrowed to those two, a {@code Station} inside it
 * stands at the field narrowed to {@code Station}, and the rule through {@code OnceKind} turns on
 * a question of its own.
 */
class AnArmOnACaseThatIsASumNarrowsToItsLeavesTest {

    private static final String MODEL = """
            module probe.several

            data Station = { code: String }
            data Hospital = { code: String }
            data Renkei
            data OnceKind = Station | Hospital
            data VisitKind = OnceKind | Renkei
            data StationOrRenkei = Station | Renkei

            let visitText (k: VisitKind): String =
                match k with
                    | OnceKind as x ->
                        match x with
                            | Station as s -> s.code
                            | Hospital as h -> h.code
                    | Renkei -> ""

            let eitherText (k: VisitKind): String =
                match k with
                    | Station | Hospital as x ->
                        match x with
                            | Station as s -> s.code
                            | Hospital as h -> h.code
                            | Renkei -> "never"
                    | Renkei -> ""

            data Visit = { kind: VisitKind }
            data Near = { kind: StationOrRenkei }

            behavior describeEither : (v: Visit) -> String
            let describeEither (v) = eitherText(v.kind)

            data Counts = { count: Int }
            data Desk = { ...Counts }
            data Ward = { ...Counts, beds: Int }
            data Staffed = Desk | Ward
            data Unit = Staffed | Renkei
            data Floor = { unit: Unit }

            behavior busy : (f: Floor) -> String
            let busy (f) =
                match f.unit with
                    | Staffed as x -> if x.count > 3 then "busy" else "quiet"
                    | Renkei -> ""

            data Low
            data Mid
            data High
            data Lowish = Low | Mid
            data Level = Lowish | High
            data Rated = { level: Level }

            behavior rate : (r: Rated) -> String
            let rate (r) =
                match r.level with
                    | Lowish as x -> if x == Mid then "mid" else "low"
                    | High -> "high"

            behavior describe : (v: Visit) -> String
            let describe (v) = visitText(v.kind)

            behavior describeNear : (n: Near) -> String
            let describeNear (n) = visitText(n.kind)

            behavior once : (v: Visit) -> String
            let once (v) =
                match v.kind with
                    | OnceKind -> "once"
                    | Renkei -> "linked"

            behavior twice : (v: Visit) -> String
            let twice (v) =
                match v.kind with
                    | OnceKind ->
                        match v.kind with
                            | OnceKind -> "once"
                            | Renkei -> "never"
                    | Renkei -> "linked"
            """;

    /** The issue's model: the names under the inner arms stand under the leaves. */
    @Test
    void theNamesUnderTheInnerArmsStandAtTheLeaves() {
        Set<String> under = underTheField(named("describe"), "v.kind");
        assertTrue(under.containsAll(Set.of("v.kind@Station.code", "v.kind@Hospital.code")),
                () -> "each case's field is read under that case: " + under);
        assertTrue(under.stream().noneMatch(each -> each.contains("}@")),
                () -> "an arm inside the narrowing narrows it rather than adding a step: " + under);
        assertTrue(under.stream().noneMatch(each -> each.contains("}.")),
                () -> "and nothing is read under the several cases as though they were one: "
                        + under);
    }

    /**
     * An arm naming the cases one by one leaves the value what an arm naming the case above them
     * does, and the names under it stand where they do under that one.
     */
    @Test
    void anArmNamingSeveralCasesNarrowsAsTheCaseAboveThemDoes() {
        Set<String> under = underTheField(named("describeEither"), "v.kind");
        assertTrue(under.containsAll(Set.of("v.kind@Station.code", "v.kind@Hospital.code")),
                () -> "each case's field is read under that case: " + under);
        List<DecisionRule> rules = rulesOf("describeEither");
        assertTrue(rules.stream().map(AnArmOnACaseThatIsASumNarrowsToItsLeavesTest::answers)
                        .anyMatch(each -> each.equals(List.of("v.kind -> {Station|Hospital}",
                                "v.kind -> Station"))),
                () -> "the rule through Station takes the arm above it: " + rules);
    }

    /**
     * An arm inside the narrowing that the narrowing leaves no value for is an answer to the same
     * question as its neighbours, and a rule no row takes.
     */
    @Test
    void anArmTheNarrowingLeavesNothingForIsARuleNoRowTakes() {
        DecisionReading.Ruled never = ruledOf("describeEither").stream()
                .filter(each -> answers(each.rule()).equals(
                        List.of("v.kind -> {Station|Hospital}", "v.kind -> Renkei")))
                .findFirst().orElse(null);
        assertNotNull(never, () -> "the inner Renkei arm is a column of the inner question: "
                + rulesOf("describeEither"));
        assertTrue(never.states().neverComesOut().isPresent(),
                () -> "and no row comes out that way: " + never);
    }

    /**
     * Where the declaration leaves one of the leaves, the arm narrows to that one and is spelled the
     * way an arm naming it outright is.
     */
    @Test
    void aNarrowingToOneLeafKeepsItsSpelling() {
        Set<String> under = underTheField(named("describeNear"), "n.kind");
        assertTrue(under.contains("n.kind@Station.code"),
                () -> "the one leaf left is the case: " + under);
        assertTrue(under.stream().noneMatch(each -> each.contains("{")),
                () -> "and nothing is spelled as a set: " + under);
    }

    /**
     * The outer fork and the inner one ask two questions of one subject, and the rule through
     * {@code Station} answers both.
     */
    @Test
    void theRuleThroughTheCaseAboveIsAColumnOfItsOwn() {
        List<DecisionRule> rules = rulesOf("describe");
        assertEquals(3, rules.size(), () -> "a rule per leaf, each named whole: " + rules);
        DecisionReading.Ruled station = ruledOf("describe").stream()
                .filter(each -> answers(each.rule()).contains("v.kind -> Station"))
                .findFirst().orElse(null);
        assertNotNull(station, () -> "a rule goes through Station: " + rules);
        assertEquals(List.of("v.kind -> {Station|Hospital}", "v.kind -> Station"),
                answers(station.rule()), "the rule through Station takes the column above it too");
        Requirements.Merge required = station.states().requirements();
        assertEquals("Station", assertInstanceOf(Requirements.Merge.Merged.class, required,
                        () -> "a row can take the way: " + required).requirements()
                        .at(TermPath.of("v").then("kind")).spelled(),
                "and what a row has to be there is both narrowings at once, which is Station");
        List<String> renkei = rules.stream().map(AnArmOnACaseThatIsASumNarrowsToItsLeavesTest::answers)
                .filter(each -> each.contains("v.kind -> Renkei")).findFirst().orElseThrow();
        assertEquals(List.of("v.kind -> Renkei"), renkei,
                "the rule beside the case answers the outer question alone");
    }

    /** A narrowing to several leaves that nothing narrows further is a rule as it stands. */
    @Test
    void anArmLeftAtSeveralLeavesIsARule() {
        assertEquals(Set.of(List.of("v.kind -> {Station|Hospital}"), List.of("v.kind -> Renkei")),
                rulesOf("once").stream()
                        .map(AnArmOnACaseThatIsASumNarrowsToItsLeavesTest::answers)
                        .collect(Collectors.toSet()));
    }

    /**
     * Two forks dividing one subject the same way are one question, however often a path meets it:
     * the way that answers it twice alike is one column, and the way that answers it both ways is
     * no rule.
     */
    @Test
    void theSameQuestionAskedTwiceIsOneColumn() {
        assertEquals(Set.of(List.of("v.kind -> {Station|Hospital}"), List.of("v.kind -> Renkei")),
                rulesOf("twice").stream()
                        .map(AnArmOnACaseThatIsASumNarrowsToItsLeavesTest::answers)
                        .collect(Collectors.toSet()));
    }

    /**
     * A value left several cases stands at the position those are cases of, and a name every case
     * spreads stands under each case.
     *
     * <p>Neither is the narrowing to the set, which is no position the input holds: compared or
     * counted at it, the value would be a number of nothing. The narrowing is what a fork on the
     * value reads, and nothing else.
     */
    @Test
    void aValueLeftSeveralCasesStandsAtItsPosition() {
        Compilation c = Compilation.ofSource(MODEL, "Main");
        c.measure(Adequacy.Asked.fullReport());
        c.answerEverything();
        assertEquals(List.of(), c.errors().stream()
                .map(e -> e.diagnostic().code().toString()).toList(), "the model is measured");

        Set<String> rated = underTheField(named("rate"), "r");
        assertTrue(rated.contains("r.level") && rated.stream().noneMatch(each -> each.contains("{")),
                () -> "the value compared is the position's: " + rated);
        Set<String> counted = underTheField(named("busy"), "f.unit");
        assertTrue(counted.containsAll(Set.of("f.unit@Desk.count", "f.unit@Ward.count"))
                        && counted.stream().noneMatch(each -> each.contains("{")),
                () -> "the shared name stands under each case: " + counted);
    }

    /**
     * The cases a narrowing leaves are said in the order the model declares them, and not in the
     * order their names compare in: renamed so that the names compare the other way round, the
     * model's rules read the same once the names are put back.
     */
    @Test
    void theCasesLeftAreSaidInTheOrderTheModelDeclaresThem() {
        Set<List<String>> asWritten = ruledOf(MODEL, "describe").stream()
                .map(each -> answers(each.rule())).collect(Collectors.toSet());
        Set<List<String>> renamed = ruledOf(MODEL.replace("Station", "Zzzzzzz")
                        .replace("Hospital", "Aaaaaaaa"), "describe").stream()
                .map(each -> answers(each.rule()).stream()
                        .map(said -> said.replace("Zzzzzzz", "Station")
                                .replace("Aaaaaaaa", "Hospital"))
                        .toList())
                .collect(Collectors.toSet());
        assertEquals(asWritten, renamed);
        assertTrue(asWritten.stream().anyMatch(each -> each.contains("v.kind -> {Station|Hospital}")),
                () -> "in the order OnceKind declares them: " + asWritten);
    }

    /**
     * A narrowing of an enumeration says on the enumeration's order the places it leaves out, and a
     * narrowing of a sum that is no enumeration says nothing there.
     */
    @Test
    void aNarrowingOfAnEnumerationLeavesItsOtherPlacesOut() {
        List<List<TakenConstraint.AwayFrom>> rated = narrowingsOnTheWay("rate");
        assertEquals(Set.of(1, 2), rated.stream().map(List::size).collect(Collectors.toSet()),
                () -> "Lowish leaves High out, and the arm beside it leaves both of Lowish's"
                        + " out: " + rated);
        assertTrue(narrowingsOnTheWay("describe").stream().allMatch(List::isEmpty),
                "a sum whose cases hold fields is ordered by nothing");
    }

    /** What each narrowing on the way to {@code behavior}'s rules leaves out of its order. */
    private static List<List<TakenConstraint.AwayFrom>> narrowingsOnTheWay(String behavior) {
        return ruledOf(behavior).stream()
                .flatMap(each -> each.states().onTheWay().stream())
                .filter(each -> each instanceof OnTheWay.Narrowed)
                .map(each -> ((OnTheWay.Narrowed) each).onItsOrder())
                .toList();
    }

    /** Each case column of {@code rule}, as its subject and what the rule came out as. */
    private static List<String> answers(DecisionRule rule) {
        return rule.inOrder().stream()
                .filter(each -> each instanceof DecidedCondition.Narrowed)
                .map(each -> (DecidedCondition.Narrowed) each)
                .map(each -> ((DecisionSubject.AnInput) each.condition().of()).at() + " -> "
                        + each.to().spelled())
                .toList();
    }

    private static List<DecisionRule> rulesOf(String behavior) {
        return ruledOf(behavior).stream().map(DecisionReading.Ruled::rule).toList();
    }

    private static List<DecisionReading.Ruled> ruledOf(String behavior) {
        return ruledOf(MODEL, behavior);
    }

    private static List<DecisionReading.Ruled> ruledOf(String model, String behavior) {
        Compilation c = Compilation.ofSource(model, "Main");
        c.measure(Adequacy.Asked.warningsAt(Adequacy.Level.ALL));
        c.answerEverything();
        assertEquals(List.of(), c.errors().stream()
                .map(e -> e.diagnostic().code() + " " + e.diagnostic().said() + " "
                        + e.diagnostic().literalMessage()).toList(), "the model is measured");
        DecisionEvidence decided = c.db().ask(new Adequacy.Decides(c.modules().get(0))).value()
                .get(behavior);
        assertNotNull(decided, () -> "the rules of " + behavior + " are read");
        List<DecisionReading.Ruled> found = decided.read().found();
        assertTrue(found.stream().allMatch(DecisionReading.Ruled::whole),
                () -> "every rule is named whole: " + found);
        return found;
    }

    /** The locations below {@code field} the body names, spelled. */
    private static Set<String> underTheField(List<TermPath> named, String field) {
        return named.stream().map(TermPath::toString)
                .filter(each -> each.startsWith(field) && !each.equals(field))
                .collect(Collectors.toSet());
    }

    /** Every location {@code behavior}'s body names, read the way its measurement reads it. */
    private static List<TermPath> named(String behavior) {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
        assertNotNull(checked, "the model under test compiles");
        Core body = checked.behaviorBodies().get(behavior);
        assertNotNull(body, () -> "the model under test writes " + behavior);
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs(module)).value()
                .get(behavior);
        InputReads reads = InputReads.ofParameters(inputs.parameterReads(), inputs.declared(rules),
                checked.elementBindings().get(behavior));
        return InputDemand.of(body, reads, rules.symbols(), rules.newtypes()).paths();
    }
}
