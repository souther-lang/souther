package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A library call the library declares computes what an operator does is worked out as that
 * operator, so the report of a comparison after it is the one the operator's gives — where a
 * declared range shows the sum fits.
 */
class ACallThatComputesAnOperatorIsReadAsThatOperatorTest {

    private static final String MODEL = """
            module probe

            data Small = Int
                invariant value >= 0 && value <= 100

            data Pair = { a: Small, b: Small }

            behavior operator : (p: Pair) -> Int
            let operator (p) = {
                let x = p.a.value + p.b.value
                Int.compare(p.a.value, p.b.value)
            }

            behavior call : (p: Pair) -> Int
            let call (p) = {
                let x = Int.add(p.a.value, p.b.value)
                Int.compare(p.a.value, p.b.value)
            }
            """;

    private static List<String> reasonsOf(Map<String, PartitionEvidence> evidence,
                                          String behavior) {
        return evidence.get(behavior).notRead().stream()
                .map(each -> each.at() + ": " + each.reason()).sorted().toList();
    }

    @Test
    void aCallReportsAsTheOperatorItComputes() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        Map<String, PartitionEvidence> evidence =
                compilation.db().ask(new Adequacy.Coverage("probe")).value();

        assertEquals(reasonsOf(evidence, "operator"), reasonsOf(evidence, "call"));
        ACompiledModel.compiles(compilation);
    }
}
