package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.meaning.MeaningsOfABody;
import souther.compiler.meaning.Proposition;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A fold whose step reads an element handed out outside it, {@code a}, beside its own element,
 * {@code b}, over the same container, asks two elements: what the step asks of {@code a} and what
 * it denies of {@code b} are met together by a container holding both. A reading that takes the
 * two for one element finds the step can never come out true, and files the fold as {@code false}.
 * The same step asked and denied of its own element alone is {@code false}.
 *
 * <p>Asked of what the reading of the body files at the fold's condition, where whether the fold
 * comes out {@code false} whatever its parts are is decided, for each kind of value a step asks:
 * a truth, a number and a string.
 */
class AFoldTellsItsOwnElementFromAnOuterOneTest {

    /** A step asking {@code %1$s} of the element named first and denying it of the second. */
    private static String fold(String asked, String first, String second) {
        String of = asked.formatted(first);
        return ("List.sum(List.map(a -> if List.fold((acc, b) -> (acc && %s) || (%s &&"
                + " Bool.not(%s)), false, x.items) then 1 else 2, x.items))")
                .formatted(of, of, asked.formatted(second));
    }

    private static final Map<String, String> ASKED = Map.of(
            "truth", "%s.paid", "number", "%s.n < 0", "string", "String.startsWith(\"X\", %s.text)");

    @Test
    void aStepAskingTwoElementsIsNeverFiledAsFalse() {
        Map<String, String> bodies = new LinkedHashMap<>();
        Map<String, Boolean> expected = new LinkedHashMap<>();
        ASKED.forEach((kind, asked) -> {
            bodies.put(kind + "Apart", fold(asked, "a", "b"));
            expected.put(kind + "Apart", false);
            bodies.put(kind + "Alike", fold(asked, "b", "b"));
            expected.put(kind + "Alike", true);
        });
        assertEquals(expected, filedFalse(bodies));
    }

    /** For each body, whether the reading filed some condition of it as {@code false}. */
    private static Map<String, Boolean> filedFalse(Map<String, String> bodies) {
        StringBuilder source = new StringBuilder("""
                module probe.fold

                data Item = { n: Int, paid: Bool, text: String }
                    invariant n >= -10 && n <= 10
                data Input = { items: List<Item> }
                """);
        bodies.forEach((name, body) -> source.append("""

                behavior %s : (x: Input) -> Int
                let %s (x) = %s
                """.formatted(name, name, body)));
        Compilation made = Compilation.ofSource(source.toString(), "Main");
        ACompiledModel.compiles(made);
        Bodies.Elaborated checked = made.db().ask(new Bodies.Checked("probe.fold")).value();
        RuleReadingSource rules = RuleReadings.of(made, "probe.fold");
        Map<String, InputDomain> inputs = made.db().ask(new Adequacy.Inputs("probe.fold"))
                .value();
        Map<String, Boolean> out = new LinkedHashMap<>();
        for (String behavior : bodies.keySet()) {
            AnalysisBody analysis = checked.analysisBodies().get(behavior);
            InputDomain input = inputs.get(behavior);
            InputReading reading = input.reading(rules);
            MeaningsOfABody meanings = MeaningsOfABodyReading.of(analysis, () -> reading,
                    InputReads.ofParametersWhereCallsStand(input.parameterReads(),
                            input.declared(rules), ElementBindings.of(analysis, rules.newtypes()),
                            input.dependencies()),
                    rules.symbols(), rules.newtypes());
            out.put(behavior, meanings.stated().values().stream().anyMatch(stated ->
                    stated.states() instanceof Proposition.Always(boolean holds) && !holds));
        }
        return out;
    }
}
