package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.InjectedAnswer;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A truth asked of a place inside what a dependency answers is written there when the answer is
 * composed.
 *
 * <p>The answer is one value with a {@code Bool} inside it, and what the way asks is which of the
 * two values stands at that place. So the value is composed holding it, whichever value was asked;
 * and asked for both, no value is.
 */
class ATruthInsideAnAnswerIsWrittenWhereItIsComposedTest {

    private static final String MODEL = """
            module example.answered

            data Reading = { ok: Bool, at: Int }

            behavior holds : (r: Reading) -> Bool
            let holds (r) = r.ok
            """;

    private static final List<TermPath.Step> OK = List.of(new TermPath.Step.Field("ok"));

    @Test
    void theValueIsComposedHoldingTheTruthAsked() {
        for (boolean held : List.of(true, false)) {
            AnAnswerComposed.Attempt attempt =
                    AnAnswerComposed.of(subject(), List.of(truth(held)));
            AnAnswerComposed.Outcome.Composed composed =
                    assertInstanceOf(AnAnswerComposed.Outcome.Composed.class, attempt.outcome(),
                            () -> "a value is composed: " + attempt);
            String written = composed.value().text();
            assertEquals(List.of("ok = " + held), fieldsNamedOk(written),
                    () -> "the value holds what was asked of the place: " + written);
        }
    }

    @Test
    void bothValuesOfThePlaceAreNoValue() {
        AnAnswerComposed.Attempt attempt =
                AnAnswerComposed.of(subject(), List.of(truth(true), truth(false)));
        assertInstanceOf(AnAnswerComposed.Outcome.NothingComposed.class, attempt.outcome(),
                () -> "no value holds both: " + attempt);
    }

    private static AnswerDemand truth(boolean held) {
        return new AnswerDemand.ATruth(
                new InjectedAnswer(new ValueName.Behavior("example.answered", "look"), List.of()),
                new ConditionReportAnchor.WhereTheReadingMetIt("m", new ConditionOccurrence("b", 0)),
                OK, held);
    }

    /** Every {@code ok = ...} written in {@code value}. */
    private static List<String> fieldsNamedOk(String value) {
        List<String> out = new ArrayList<>();
        for (String part : value.split("[{},]")) {
            if (part.trim().startsWith("ok =")) {
                out.add(part.trim());
            }
        }
        return out;
    }

    private static final Compilation COMPILATION = compiled();

    private static Compilation compiled() {
        Compilation made = Compilation.ofSource(MODEL, "Main");
        made.measure(Adequacy.Asked.fullReport());
        made.answerEverything();
        return made;
    }

    /** One position standing for a {@code Reading}, the shape an answer's subject has. */
    private static MeasuredInput subject() {
        String module = COMPILATION.modules().getFirst();
        InputDomain domain = COMPILATION.db().ask(new Adequacy.Inputs(module)).value()
                .get("holds");
        assertNotNull(domain, "the model under test compiles");
        Partitions.Partitioning divided =
                COMPILATION.db().ask(new Adequacy.Divided(module, "holds")).value();
        assertNotNull(divided, "the model under test is measured");
        return MeasuredInput.of("holds", domain.reading(RuleReadings.of(COMPILATION, module)),
                divided);
    }
}
