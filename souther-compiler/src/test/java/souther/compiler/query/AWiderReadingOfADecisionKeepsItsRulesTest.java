package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.TermPath;
import souther.compiler.partition.CaseCandidates;
import souther.compiler.partition.DecisionReading;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

/**
 * The decision of a behavior read under a reading of the input closed over more places states the
 * same rules as the one the measurement was made with.
 *
 * <p>A search for a row builds a candidate against the wider reading and judges it against the
 * rules the rows were placed at, which are the measured reading's. The two are joined by a rule
 * being equal to a rule, so what a wider reading adds has to be ways to cases and no rule that the
 * measured one does not state, nor one it states that the wider one lost.
 */
class AWiderReadingOfADecisionKeepsItsRulesTest {

    private static final String NODE = """
            module m
            data Node = { v: Int, below: List<Node> }
            data Yes
            data No
            data Big
            let anyBig (n: Node): Bool = n.v > 5 || List.any(c -> anyBig(c), n.below)
            """;

    private static final List<TermPath> THREE_LEVELS_DOWN = levelsDown(3);

    private static List<TermPath> levelsDown(int levels) {
        List<TermPath> out = new ArrayList<>();
        TermPath node = TermPath.of("t");
        for (int level = 0; level < levels; level++) {
            TermPath container = node.then("below");
            node = container.element();
            out.add(container);
            out.add(node);
            out.add(node.then("v"));
        }
        return out;
    }

    @Test
    void aDecisionOfOneRuleStatesItUnderAWiderReading() {
        assertSameRules(NODE + """
                behavior f : (t: Node) -> Yes | No
                let f (t) = if anyBig(t) then Yes else No
                """);
    }

    @Test
    void aDecisionOfSeveralRulesStatesThemAllUnderAWiderReading() {
        assertSameRules(NODE + """
                behavior f : (t: Node) -> Big | Yes | No
                let f (t) = if t.v > 100 then Big else if anyBig(t) then Yes else No
                """);
    }

    @Test
    void aDecisionWhoseRulesConsultTheNodesBelowStatesThemUnderAWiderReading() {
        assertSameRules(NODE + """
                behavior f : (t: Node) -> Yes | No
                let f (t) = if List.all(c -> c.v <= 5, t.below) && anyBig(t) then Yes else No
                """);
    }

    @Test
    void theWiderReadingReadsMorePlacesThanTheMeasurement() {
        Compilation compilation = measured(NODE + """
                behavior f : (t: Node) -> Yes | No
                let f (t) = if anyBig(t) then Yes else No
                """);
        String module = compilation.modules().getFirst();
        InputDomain narrow = compilation.db().ask(new Adequacy.Inputs(module)).value().get("f");
        InputDomain wide = Adequacy.InputsOf.readingWith(compilation.db(), module, "f",
                THREE_LEVELS_DOWN).value();
        TermPath grandchild = THREE_LEVELS_DOWN.get(5);
        assertEquals(false, CaseCandidates.reads(narrow, grandchild), "the measurement stops short");
        assertEquals(true, CaseCandidates.reads(wide, grandchild), "the wider reading reads it");
        assertNotEquals(narrow.positions().size(), wide.positions().size());
    }

    private static Compilation measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }

    private static void assertSameRules(String source) {
        Compilation compilation = measured(source);
        String module = compilation.modules().getFirst();
        DecisionReading narrow = compilation.db().ask(new Adequacy.Decides(module)).value()
                .get("f").read();
        InputDomain domain = Adequacy.InputsOf.readingWith(compilation.db(), module, "f",
                THREE_LEVELS_DOWN).value();
        DecisionReading wide = Adequacy.DecisionReadings.over(compilation.db(), "f",
                compilation.db().ask(new Bodies.Observable(module)).value().analysisBodies()
                        .get("f"),
                domain, Shapes.ruleReading(compilation.db(), module).value(),
                CaseCandidates.OF_THE_SEARCH);

        assertFalse(narrow.rules().isEmpty(), "the decision was read, or this compares nothing");
        assertEquals(narrow.rules(), wide.rules(),
                "the same rules, in the same order, under a reading of more places");
    }
}
