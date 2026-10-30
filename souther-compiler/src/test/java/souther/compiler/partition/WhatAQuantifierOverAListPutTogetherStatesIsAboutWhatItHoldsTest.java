package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.core.Core;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReads;
import souther.compiler.meaning.Proposition;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

/**
 * What {@code List.any} and {@code List.all} state of a list an operation put together of a list
 * written out is what they state of the elements that list holds: a flatMap's as the list written
 * end to end, and a filter's as the elements it keeps.
 *
 * <p>The truth of the whole call, read through the operation's law over each element written out
 * — which is the reading a fork on it is decided by, beside the reading of the comparison inside the
 * closure that a line is drawn on.
 */
class WhatAQuantifierOverAListPutTogetherStatesIsAboutWhatItHoldsTest {

    private static final String BOTH = "[Placement { who = Alice, room = 1 },"
            + " Placement { who = Bob, room = 2 }]";

    private static final String ALICE = "[Placement { who = Alice, room = 1 }]";

    private static final String ANY = "List.any(p -> p.who == who, %s)";

    private static final String ALL = "List.all(p -> p.who /= who, %s)";

    @Test
    void aFlatMapStatesWhatTheListWrittenOutStates() {
        assertEquals(stated(ANY.formatted(BOTH)).spelledOut(), stated(ANY.formatted(
                "List.flatMap(s -> [Placement { who = s, room = 1 }], [Alice, Bob])")).spelledOut());
    }

    @Test
    void anyOverAFilterStatesWhatItStatesOfTheElementsKept() {
        String kept = "List.filter(p -> p.room == 1, %s)".formatted(BOTH);
        assertEquals(stated(ANY.formatted(ALICE)).spelledOut(), stated(ANY.formatted(kept)).spelledOut());
        assertNotEquals(stated(ANY.formatted(BOTH)).spelledOut(), stated(ANY.formatted(kept)).spelledOut(),
                "the element dropped is one the statement would otherwise be about");
    }

    @Test
    void allOverAFilterStatesWhatItStatesOfTheElementsKept() {
        String kept = "List.filter(p -> p.room == 1, %s)".formatted(BOTH);
        assertEquals(stated(ALL.formatted(ALICE)).spelledOut(), stated(ALL.formatted(kept)).spelledOut());
        assertNotEquals(stated(ALL.formatted(BOTH)).spelledOut(), stated(ALL.formatted(kept)).spelledOut(),
                "the element dropped is one the statement would otherwise be about");
    }

    /** What the condition of the fork on {@code truth} states. */
    private static Proposition stated(String truth) {
        String source = """
                module p
                data Suspect = Alice | Bob | Carol
                data Placement = { who: Suspect, room: Int }
                behavior f : (who: Suspect) -> Int
                let f (who) = if %s then 1 else 0
                """.formatted(truth);
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the model under test compiles");
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked("p")).value();
        AnalysisBody analysis = checked.analysisBodies().get("f");
        RuleReadingSource rules = RuleReadings.of(compilation, "p");
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs("p")).value().get("f");
        InputReads reads = InputReads.ofParametersWhereCallsStand(inputs.parameterReads(),
                inputs.declared(rules), ElementBindings.of(analysis, rules.newtypes()),
                inputs.dependencies());
        Core e = Core.withoutStanding(analysis.core());
        while (e instanceof Core.LetIn let) {
            reads = reads.and(let.binder(), let.value());
            e = Core.withoutStanding(let.body());
        }
        Core.If fork = assertInstanceOf(Core.If.class, e, "the body is one fork");
        return Pullback.ofATruth(fork.cond(), reads, inputs.reading(rules), Optional.empty())
                .proposition();
    }
}
