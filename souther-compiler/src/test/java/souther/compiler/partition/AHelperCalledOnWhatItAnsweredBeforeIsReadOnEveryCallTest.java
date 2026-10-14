package souther.compiler.partition;

import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.ValueSource;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReads;
import souther.compiler.meaning.MeaningsOfABody;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.WhyUnread;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A helper called on what its earlier calls answered has its comparison read on every call.
 *
 * <p>The third call compares what the second answered, which is chosen by the second's
 * {@code if}, whose arms are made of what the first answered, chosen by the first's. A reading goes
 * into each choice once and reads the comparison on each way through both; nothing about that is
 * past any figure — two choices of two arms are four readings. Where the reading lost the first
 * choice on its way into the second, the comparison stopped at a choice it had gone into, and the
 * report called that a figure of this compiler's.
 */
class AHelperCalledOnWhatItAnsweredBeforeIsReadOnEveryCallTest {

    /** A model drawing {@code calls} allowances in turn through one helper. */
    private static String drawing(int calls) {
        StringBuilder held = new StringBuilder();
        StringBuilder drawn = new StringBuilder();
        StringBuilder body = new StringBuilder();
        StringBuilder built = new StringBuilder();
        String used = "used";
        for (int at = 0; at < calls; at++) {
            String allowance = "allowance" + at;
            held.append(at == 0 ? "" : ", ").append(allowance).append(": MB");
            drawn.append(at == 0 ? "" : ", ").append("from").append(at).append(": MB");
            body.append("    let (a").append(at).append(", rest").append(at).append(") = take(")
                    .append(used).append(", held.").append(allowance).append(")\n");
            built.append(at == 0 ? "" : ", ").append("from").append(at).append(" = a").append(at);
            used = "rest" + at;
        }
        return """
                module probe.drawing

                data MB = Int
                    invariant value >= 0
                data Held = { %s }
                data Drawn = { %s, throttled: MB }

                behavior draw : (used: MB, held: Held) -> Drawn
                    constructs Drawn, MB

                let draw (used, held) = {
                %s    Drawn { %s, throttled = %s }
                }

                let take (used: MB, cap: MB): (MB, MB) =
                    if used.value <= cap.value then (used, MB(0)) else (cap, MB(used.value - cap.value))
                """.formatted(held, drawn, body, built, used);
    }

    /** What every comparison of {@code behavior}'s body states, filed at each place it is met. */
    private static Map<MeaningsOfABody.Site, Proposition> statedBy(String source,
                                                                   String behavior) {
        String module = source.lines().findFirst().orElseThrow().substring("module ".length());
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().literalMessage())
                .toList(), "the model compiles");
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
        assertNotNull(checked, "the model under test compiles");
        AnalysisBody analysis = checked.analysisBodies().get(behavior);
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        InputDomain inputs =
                compilation.db().ask(new Adequacy.Inputs(module)).value().get(behavior);
        InputReads reads = InputReads.ofParametersWhereCallsStand(inputs.parameterReads(),
                inputs.declared(rules), ElementBindings.of(analysis, rules.newtypes()),
                inputs.dependencies());
        MeaningsOfABody meanings = MeaningsOfABodyReading.of(analysis,
                () -> inputs.reading(rules), reads, rules.symbols(), rules.newtypes());
        Map<MeaningsOfABody.Site, Proposition> out = new LinkedHashMap<>();
        meanings.stated().forEach((site, meaning) -> {
            if (site.part() == MeaningsOfABody.Part.Asked.ITSELF) {
                out.put(site, meaning.states());
            }
        });
        return out;
    }

    /** What stopped each comparison that stopped, in the order they are met. */
    private static List<WhyUnread> stops(Map<MeaningsOfABody.Site, Proposition> stated) {
        List<WhyUnread> out = new ArrayList<>();
        for (Proposition said : stated.values()) {
            WhyUnread why = Proposition.firstStopIn(said);
            if (why != null) {
                out.add(why);
            }
        }
        return out;
    }

    /** One comparison for each call, and every one of them read to the end. */
    @ParameterizedTest
    @ValueSource(ints = {3, 4})
    void everyCallsComparisonIsRead(int calls) {
        Map<MeaningsOfABody.Site, Proposition> stated = statedBy(drawing(calls), "draw");
        assertEquals(calls, stated.size(), () -> "one comparison for each call: " + stated);
        assertEquals(List.of(), stops(stated), stated::toString);
    }

}
