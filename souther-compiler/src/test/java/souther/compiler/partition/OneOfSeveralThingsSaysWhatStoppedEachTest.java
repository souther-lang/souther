package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.meaning.WhyNotTaken;
import souther.compiler.meaning.WhyUnread;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * One of several things declined as a row's demand says what stopped each of them, however the
 * disjunction was written.
 *
 * <p>A disjunction written with {@code ||} is two conditions of the shape; the same disjunction
 * written as a denied conjunction is one condition whose proposition is the disjunction. Both name
 * no part a row is asked for, and both say why each part could not have been asked besides — one
 * part's meaning unread, another a quantifier this reading has no words for. Only the parts that
 * could be what holds: coming out false, the two are a conjunction and each part is asked.
 */
class OneOfSeveralThingsSaysWhatStoppedEachTest {

    private static final String MODEL = """
            module example.oneof

            data Line = { price: Int }

            data Order = { x: Int, y: Int, floor: Int, lines: List<Line> }

            behavior written : (o: Order) -> Bool
            let written (o) = o.x * o.y > 4 || List.all(l -> l.price > o.floor, o.lines)

            behavior denied : (o: Order) -> Bool
            let denied (o) =
                Bool.not(o.x * o.y <= 4 && List.any(l -> l.price <= o.floor, o.lines))
            """;

    /** What the walk declined, and why, in the order it met them. */
    private static List<WhyNotTaken> whys(String behavior, boolean holding) {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.answerEverything();
        String module = compilation.modules().getFirst();
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
        assertNotNull(checked, "the model under test compiles");
        // The tree the analysis reads, where the language's operations still stand as written.
        AnalysisBody analysis = checked.analysisBodies().get(behavior);
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs(module)).value().get(behavior);
        InputReads reads = InputReads.ofParametersWhereCallsStand(inputs.parameterReads(),
                inputs.declared(rules), ElementBindings.of(analysis, rules.newtypes()),
                inputs.dependencies());
        InputReading read = inputs.reading(rules);
        return ReachingCuts.stating(Condition.of(analysis.core(), reads, rules.symbols(),
                        rules.newtypes(), new ConditionNumbering(module, behavior)), read, holding,
                        new WhatConditionsState(read)).stream()
                .filter(each -> each instanceof OnTheWay.Declined)
                .flatMap(each -> ((OnTheWay.Declined) each).whys().stream())
                .toList();
    }

    @Test
    void aDisjunctionSaysWhatStoppedEachPart() {
        assertEquals(List.of(
                        new WhyNotTaken.ProjectionIncomplete(WhyNotTaken.Shape.ONE_OF_SEVERAL_THINGS),
                        new WhyNotTaken.MeaningUnread(new WhyUnread.OutsideTheLinearFragment()),
                        new WhyNotTaken.ProjectionIncomplete(
                                WhyNotTaken.Shape.EVERY_ELEMENT_AND_MORE)),
                whys("written", true));
        assertEquals(List.of(
                        new WhyNotTaken.MeaningUnread(new WhyUnread.OutsideTheLinearFragment())),
                whys("written", false), "coming out false, each part is asked");
    }

    @Test
    void aDeniedConjunctionSaysWhatTheDisjunctionItMeansSays() {
        for (boolean holding : List.of(true, false)) {
            assertEquals(whys("written", holding), whys("denied", holding),
                    "coming out " + holding);
        }
    }
}
