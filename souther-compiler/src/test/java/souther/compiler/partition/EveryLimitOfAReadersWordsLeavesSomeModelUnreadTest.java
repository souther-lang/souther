package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.PathReachability;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.diag.SourcePos;
import souther.compiler.flow.AWayThrough;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.Unsettlement;
import souther.compiler.meaning.MeaningsOfABody;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.WhyNotTaken;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.reach.Reachability;
import souther.compiler.reach.WhyUnsettled;

import java.util.EnumMap;
import java.util.EnumSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Every limit of a reader's words is met by a model, and the model says which statements it leaves
 * that reader without words for.
 *
 * <p>A limit is a fact about a domain — the input's positions a row is written at, or what a path
 * knows — and a fact about a domain is one a model can run into. So each has a behavior here that
 * the reader whose domain it is declines for it: the readers of what a row is asked
 * ({@link DemandReading#asked}, {@link DecisionMeanings#columnOf},
 * {@link WhatTheRulesLeave#admits}) for the input's words, and the walk of a path, through what it
 * answers about the arms past a condition, for what a path knows.
 *
 * <p><b>Total over the limits, by the enum and not by a list here.</b> A limit added without a model
 * is a failure, which is the question put to whoever added it: a limit no model reaches is one to
 * take out of the vocabulary or to give a way in, and an entry saying it needs neither would make
 * this agree that a domain may have an edge nobody can stand at.
 */
class EveryLimitOfAReadersWordsLeavesSomeModelUnreadTest {

    private static final String MODEL = """
            module probe.edges

            data Tier = Gold | Plain
            data Item = { n: Int }
            data P = { n: Int }
            data O = { a: Int, b: Int, name: String, other: String, tier: Tier,
                       xs: List<Item>, p: P, q: P }

            data A
            data B
            data C

            behavior lookup : (n: Int) -> Int

            behavior twoRecords : (o: O) -> A | B | C
            let twoRecords (o) = if o.p == o.q then (if o.a > 5 then A else B) else C

            behavior askedOfADependency : (o: O) -> A | B | C depends on lookup
            let askedOfADependency (o, lookup) =
                if lookup(o.a) > 3 then (if o.a > 5 then A else B) else C

            let farOut (o: O): Bool = o.a > 5 || o.a < -5
            let allDear (xs: List<Item>): Bool = List.all(i -> i.n > 3, xs)
            let isGold (t: Tier): Bool =
                match t with
                    | Gold -> true
                    | Plain -> false
            let named (o: O): Bool = List.contains(o.name, [o.other])

            behavior oneOfTwo : (o: O) -> A | B | C
            let oneOfTwo (o) = if farOut(o) then (if o.a > 9 then A else B) else C

            behavior everyItem : (o: O) -> A | B | C
            let everyItem (o) = if allDear(o.xs) then (if o.a > 5 then A else B) else C

            behavior aCase : (o: O) -> A | B | C
            let aCase (o) = if isGold(o.tier) then (if o.a > 5 then A else B) else C

            behavior oneValue : (o: O) -> A | B | C
            let oneValue (o) = if named(o) then (if o.a > 5 then A else B) else C

            behavior anOrder : (o: O) -> A | B | C
            let anOrder (o) = if o.name < "M" then (if o.a > 5 then A else B) else C

            behavior aCount : (o: O) -> A | B | C
            let aCount (o) =
                if List.length(List.filter(i -> i.n > 3, o.xs)) == 2
                then (if o.a > 5 then A else B) else C

            behavior twoTexts : (o: O) -> A | B | C
            let twoTexts (o) = if o.name == o.other then (if o.a > 5 then A else B) else C

            let sq (d: Decimal): Decimal = d * d
            %s
            let tight (n: Decimal, m: Decimal): Bool = n + t62 * m > 0.5m

            data Common = { d: Decimal }
            data First = { ...Common, x: Int }
            data Second = { ...Common, y: Int }
            data Spread = First | Second

            behavior aNameAndItsCase : (s: Spread) -> A | B | C
            let aNameAndItsCase (s) =
                match s with
                    | First as f -> if tight(s.d, f.d) then A else B
                    | Second -> C
            """.formatted(squarings());

    /** {@code t0} a tenth and each {@code tN} the square of the one before: a weight a ratio
     *  holds, which added to one is a number none does. */
    private static String squarings() {
        StringBuilder lets = new StringBuilder("let t0 = 0.1m\n");
        for (int i = 1; i <= 62; i++) {
            lets.append("let t").append(i).append(" = sq(t").append(i - 1).append(")\n");
        }
        return lets.toString();
    }

    /** The behavior each limit leaves without words. */
    private static Map<WhyNotTaken.DomainLimit, String> witnesses() {
        Map<WhyNotTaken.DomainLimit, String> out = new EnumMap<>(WhyNotTaken.DomainLimit.class);
        // Two records compared: read to the end, and a difference that is a distance on nothing.
        out.put(WhyNotTaken.DomainLimit.A_QUANTITY_ON_NO_ORDER, "twoRecords");
        // What a dependency answered, which a row stands in and does not write.
        out.put(WhyNotTaken.DomainLimit.AN_ANSWER_A_ROW_STANDS_IN, "askedOfADependency");
        // A helper whose answer is one of two comparisons: a path holds facts that all hold.
        out.put(WhyNotTaken.DomainLimit.A_PATH_KNOWS_NO_ALTERNATIVES, "oneOfTwo");
        // A helper whose answer is every element meeting something, which a path holds only as
        // the closure it was written with.
        out.put(WhyNotTaken.DomainLimit.A_PATH_HOLDS_ELEMENT_FACTS_AS_WRITTEN, "everyItem");
        // A helper whose answer is which case a value is.
        out.put(WhyNotTaken.DomainLimit.A_PATH_KNOWS_NO_CASES, "aCase");
        // A helper whose answer is two texts being one.
        out.put(WhyNotTaken.DomainLimit.A_PATH_KNOWS_NO_SAMENESS_OF_VALUES, "oneValue");
        // A text against a written place on its order.
        out.put(WhyNotTaken.DomainLimit.A_PATH_KNOWS_NO_PLACE_ON_AN_ORDER, "anOrder");
        // How many elements meet something, against a number.
        out.put(WhyNotTaken.DomainLimit.A_PATH_KNOWS_NO_COUNT_OF_ELEMENTS, "aCount");
        // Two texts compared as numbers: no place of the tree a path walks is either of them.
        out.put(WhyNotTaken.DomainLimit.A_PLACE_THE_PATH_DOES_NOT_READ, "twoTexts");
        // A name the cases spread and the same name under the case, which are one fact on a path,
        // weighed one and a fine fraction: their weights add to a number no ratio holds.
        out.put(WhyNotTaken.DomainLimit.A_NUMBER_THE_PATH_CANNOT_HOLD, "aNameAndItsCase");
        return out;
    }

    private static final Compilation COMPILATION = compiled();

    private static Compilation compiled() {
        Compilation made = Compilation.ofSource(MODEL, "Main");
        made.measure(Adequacy.Asked.fullReport());
        made.answerEverything();
        assertEquals(List.of(), made.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the model compiles");
        return made;
    }

    @Test
    void everyLimitHasAModel() {
        assertEquals(EnumSet.allOf(WhyNotTaken.DomainLimit.class), witnesses().keySet(),
                "a limit of a reader's words that no model here runs into");
    }

    @Test
    void eachModelIsLeftUnreadForItsLimit() {
        witnesses().forEach((limit, behavior) -> {
            Set<WhyNotTaken.DomainLimit> met = switch (limit.domain()) {
                case WHAT_A_ROW_IS_WRITTEN_IN -> whereARowsWordsStop(behavior);
                case WHAT_A_PATH_KNOWS -> whereAPathsWordsStop(behavior);
            };
            assertTrue(met.contains(limit),
                    () -> behavior + " is left without words for " + limit + ", and met " + met);
        });
    }

    /** What the readers of a row decline the statements of {@code behavior} for, either way. */
    private static Set<WhyNotTaken.DomainLimit> whereARowsWordsStop(String behavior) {
        Bodies.Elaborated checked =
                COMPILATION.db().ask(new Bodies.Checked("probe.edges")).value();
        AnalysisBody analysis = checked.analysisBodies().get(behavior);
        assertNotNull(analysis, () -> "the model writes " + behavior);
        RuleReadingSource rules = RuleReadings.of(COMPILATION, "probe.edges");
        InputDomain input = COMPILATION.db().ask(new Adequacy.Inputs("probe.edges")).value()
                .get(behavior);
        InputReading reading = input.reading(rules);
        MeaningsOfABody meanings = MeaningsOfABodyReading.of(analysis, () -> reading,
                InputReads.ofParametersWhereCallsStand(input.parameterReads(),
                        input.declared(rules), ElementBindings.of(analysis, rules.newtypes()),
                        input.dependencies()),
                rules.symbols(), rules.newtypes());
        Set<WhyNotTaken.DomainLimit> out = new LinkedHashSet<>();
        meanings.stated().values().forEach(stated -> {
            Proposition states = stated.states();
            for (boolean way : List.of(true, false)) {
                DemandReading.asked(way ? states : states.denied(), reading)
                        .forEach(read -> limitsIn(read, out));
                if (DecisionMeanings.columnOf(states, way, new ConditionOccurrence(behavior, 0))
                        instanceof DecidedCondition.Unread(var condition, boolean _)) {
                    condition.whys().forEach(why -> limitOf(why, out));
                }
                if (WhatTheRulesLeave.admits(states, way, reading)
                        instanceof AWayThrough.NotRuledOut(var notAsked)) {
                    notAsked.forEach(why -> limitOf(why, out));
                }
            }
        });
        return out;
    }

    private static void limitsIn(DemandReading.Read read, Set<WhyNotTaken.DomainLimit> into) {
        switch (read) {
            case DemandReading.Read.Unread(var whys) -> whys.forEach(why -> limitOf(why, into));
            case DemandReading.Read.OneOf(var alternatives) ->
                    alternatives.forEach(each -> each.forEach(one -> limitsIn(one, into)));
            case DemandReading.Read.Demands _, DemandReading.Read.Settled _,
                 DemandReading.Read.Narrows _ -> { }
        }
    }

    /** What the walk of a path past the conditions of {@code behavior} could not take in. */
    private static Set<WhyNotTaken.DomainLimit> whereAPathsWordsStop(String behavior) {
        Map<String, PathReachability.Answers> byBehavior =
                COMPILATION.db().ask(new Adequacy.PathReached("probe.edges")).value();
        assertNotNull(byBehavior.get(behavior), () -> "the walk answers about " + behavior);
        Set<WhyNotTaken.DomainLimit> out = new LinkedHashSet<>();
        byBehavior.get(behavior).found().values().forEach(reach -> {
            if (reach instanceof Reachability.Unsettled(WhyUnsettled why)) {
                why.said(new NotTaken()).forEach(each -> limitOf(each, out));
            }
        });
        return out;
    }

    private static void limitOf(WhyNotTaken why, Set<WhyNotTaken.DomainLimit> into) {
        if (why instanceof WhyNotTaken.OutsideDomain(var limit)) {
            into.add(limit);
        }
    }

    /** What a condition on the way was not taken in for, where that is why a place is open. */
    private static final class NotTaken implements WhyUnsettled.Words<List<WhyNotTaken>> {

        @Override
        public List<WhyNotTaken> noWitness() {
            return List.of();
        }

        @Override
        public List<WhyNotTaken> aConditionWasNotRead(SourcePos at, List<WhyNotTaken> why) {
            return why;
        }

        @Override
        public List<WhyNotTaken> thePositionDidNotSettleIt(Unsettlement why) {
            return List.of();
        }

        @Override
        public List<WhyNotTaken> theWalkDidNotReachIt() {
            return List.of();
        }
    }
}
