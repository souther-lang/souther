package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.core.Core;
import souther.compiler.flow.AWayThrough;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.meaning.Proposition;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A condition over what a container's elements meet, over values a body bound, or over how many an
 * operation answers is read to the end, and every reader takes it: what a row is asked, the column
 * of the decision it is, and whether the rules leave a way through it.
 *
 * <p>The shapes are the ones the readers have to be held to together: a statement of every element
 * that turns on nothing of the element, an element against a number beside it, a quantifier inside
 * one, a truth of each element, sums and products and choices of bound numbers, and the size of a
 * mapped, filtered or taken list. Where a row is not composed toward the statement the run decides
 * it, which is a statement read and not a part left unread.
 */
class EveryShapeOfAConditionOverAContainerABoundValueOrASizeIsReadToTheEndTest {

    private static final String MODEL = """
            module probe.shapes

            data Line = { price: Int, paid: Bool }
            data Group = { items: List<Line> }
            data Order = { lines: List<Line>, groups: List<Group>, floor: Int, ceil: Int }

            behavior everyLineBesideTheFloor : (o: Order) -> Bool
            let everyLineBesideTheFloor (o) = List.all(l -> o.floor > 3, o.lines)

            behavior theFloorOrNoLines : (o: Order) -> Bool
            let theFloorOrNoLines (o) = o.floor > 3 || List.isEmpty(o.lines)

            behavior everyLineAboveTheFloor : (o: Order) -> Bool
            let everyLineAboveTheFloor (o) = List.all(l -> l.price > o.floor, o.lines)

            behavior someLineAboveTheFloor : (o: Order) -> Bool
            let someLineAboveTheFloor (o) = List.any(l -> l.price > o.floor, o.lines)

            behavior someItemOfSomeGroup : (o: Order) -> Bool
            let someItemOfSomeGroup (o) = List.any(g -> List.any(x -> x.price > 3, g.items), o.groups)

            behavior everyItemOfEveryGroup : (o: Order) -> Bool
            let everyItemOfEveryGroup (o) =
                List.all(g -> List.all(x -> x.price > 3, g.items), o.groups)

            behavior someLinePaid : (o: Order) -> Bool
            let someLinePaid (o) = List.any(l -> l.paid, o.lines)

            behavior everyLinePaid : (o: Order) -> Bool
            let everyLinePaid (o) = List.all(l -> l.paid, o.lines)

            behavior aProduct : (o: Order) -> Bool
            let aProduct (o) = {
                let area = o.floor * o.ceil
                area > 4
            }

            behavior aSum : (o: Order) -> Bool
            let aSum (o) = {
                let t = o.floor + o.ceil
                t > 4
            }

            behavior twoProducts : (o: Order) -> Bool
            let twoProducts (o) = {
                let a = o.floor * o.floor
                let b = o.ceil * o.ceil
                a > b
            }

            behavior aChoice : (o: Order) -> Bool
            let aChoice (o) = {
                let m = Int.max(o.floor, o.ceil)
                m > 4
            }

            behavior theSizeOfAMap : (o: Order) -> Bool
            let theSizeOfAMap (o) = List.length(List.map(l -> l.price, o.lines)) >= 1

            behavior theSizeOfAFilter : (o: Order) -> Bool
            let theSizeOfAFilter (o) = List.length(List.filter(l -> l.price > 3, o.lines)) >= 1

            behavior oneKept : (o: Order) -> Bool
            let oneKept (o) = List.length(List.filter(l -> l.price > 3, o.lines)) == 1

            behavior theSizeOfATake : (o: Order) -> Bool
            let theSizeOfATake (o) = List.length(List.take(o.floor, o.lines)) >= 1

            behavior nothingTaken : (o: Order) -> Bool
            let nothingTaken (o) = List.isEmpty(List.take(o.floor, o.lines))

            behavior theSizeAgainstANumber : (o: Order) -> Bool
            let theSizeAgainstANumber (o) = List.length(o.lines) > o.floor
            """;

    private static final List<String> SHAPES = List.of("everyLineBesideTheFloor",
            "theFloorOrNoLines", "everyLineAboveTheFloor", "someLineAboveTheFloor",
            "someItemOfSomeGroup", "everyItemOfEveryGroup", "someLinePaid", "everyLinePaid",
            "aProduct", "aSum", "twoProducts", "aChoice", "theSizeOfAMap", "theSizeOfAFilter",
            "oneKept", "theSizeOfATake", "nothingTaken", "theSizeAgainstANumber");

    @Test
    void everyReaderTakesEveryShapeWithNothingLeftUnread() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.answerEverything();
        String module = compilation.modules().getFirst();
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
        assertNotNull(checked, () -> "the model under test compiles: " + compilation.errors());
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        List<String> unread = new ArrayList<>();
        for (String name : SHAPES) {
            AnalysisBody analysis = checked.analysisBodies().get(name);
            InputDomain inputs = compilation.db().ask(new Adequacy.Inputs(module)).value()
                    .get(name);
            InputReads reads = InputReads.ofParametersWhereCallsStand(inputs.parameterReads(),
                    inputs.declared(rules), ElementBindings.of(analysis, rules.newtypes()),
                    inputs.dependencies());
            InputReading read = inputs.reading(rules);
            Core body = analysis.core();
            Condition condition = Condition.of(body, reads, rules.symbols(), rules.newtypes(),
                    new ConditionNumbering(module, name));
            WhatConditionsState conditions = WhatConditionsState.of(read);
            Proposition stated = DemandReading.statedBy(condition, read, conditions);
            if (!Proposition.stopsIn(stated).isEmpty()) {
                unread.add(name + " leaves " + Proposition.stopsIn(stated) + " unread");
            }
            for (boolean holding : List.of(true, false)) {
                for (OnTheWay asked : ReachingCuts.stating(condition, read, holding, conditions)) {
                    declined(asked, name + " asked of a row coming out " + holding, unread);
                }
                if (DecisionMeanings.columnOf(stated, holding, new ConditionOccurrence(name, 0))
                        instanceof DecidedCondition.Unread(var column, boolean _)) {
                    unread.add(name + " is no column coming out " + holding + ": "
                            + column.whys());
                }
                if (WhatTheRulesLeave.admits(stated, holding, read)
                        instanceof AWayThrough.NotRuledOut(var notAsked) && !notAsked.isEmpty()) {
                    unread.add(name + " leaves a way unasked coming out " + holding + ": "
                            + notAsked);
                }
            }
        }
        assertEquals(List.of(), unread);
    }

    /** Adds where {@code asked}, or an alternative inside it, was declined. */
    private static void declined(OnTheWay asked, String what, List<String> into) {
        switch (asked) {
            case OnTheWay.Declined declined -> into.add(what + " was declined: " + declined.whys());
            case OnTheWay.OneOf oneOf -> oneOf.alternatives()
                    .forEach(each -> each.forEach(one -> declined(one, what, into)));
            case OnTheWay.TakenIn _, OnTheWay.Narrowed _, OnTheWay.Settled _ -> { }
        }
    }
}
