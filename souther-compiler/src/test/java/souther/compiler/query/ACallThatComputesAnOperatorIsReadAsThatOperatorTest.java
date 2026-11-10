package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.UndividedPosition;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A library call the library declares computes what an operator does is worked out as that
 * operator, so the report of a comparison after it is the one the operator's gives — where a
 * declared range shows the sum fits, and where nothing does.
 */
class ACallThatComputesAnOperatorIsReadAsThatOperatorTest {

    private static String model(String number) {
        return """
                module probe

                data Small = Int
                    invariant value >= 0 && value <= 100

                data Pair = { a: Small, b: Small, i: Int, j: Int }

                behavior ranged : (p: Pair) -> Int
                let ranged (p) = {
                    let x = %s
                    Int.compare(p.a.value, p.b.value)
                }
                """.formatted(number);
    }

    private static Map<String, UndividedPosition.Reason> reasonsOf(String number) {
        Compilation compilation = Compilation.ofSource(model(number), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        Map<String, PartitionEvidence> evidence =
                compilation.db().ask(new Adequacy.Coverage("probe")).value();
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), compilation.errors().toString());
        Map<String, UndividedPosition.Reason> byPlace = new LinkedHashMap<>();
        evidence.get("ranged").notRead().forEach(each -> byPlace.put(each.at(), each.reason()));
        return byPlace;
    }

    @Test
    void aCallReportsAsTheOperatorItComputes() {
        for (String[] pair : new String[][] {
                {"p.a.value + p.b.value", "Int.add(p.a.value, p.b.value)"},
                {"p.a.value - p.b.value", "Int.subtract(p.a.value, p.b.value)"},
                {"p.a.value * 3", "Int.multiply(p.a.value, 3)"},
                {"p.i + p.j", "Int.add(p.i, p.j)"},
                {"p.i - p.j", "Int.subtract(p.i, p.j)"}}) {
            assertEquals(reasonsOf(pair[0]), reasonsOf(pair[1]), pair[1]);
        }
    }
}
