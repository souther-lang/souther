package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.OfferingRequest;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A body over a list that calls no behavior has no row of a callee to start the list's elements
 * from. What stands for the element's type is what they start from, as the type's own decoder
 * builds it, so the row that tells the body from one answering a constant is still offered whatever
 * the element is, and one no list tells from the constant is not given a row.
 */
class ABodyThatCallsNoBehaviorIsOfferedAListOfOneElementTest {

    private static final String MODEL = """
            module repro.nocallee

            %s
            behavior f : (xs: List<%s>) -> %s

            let f (xs) = %s

            example f
                | ([]) -> %s
            """;

    private record Case(String declarations, String element, String result, String body,
                        String answeredAtNone) {}

    private static final List<Case> BODIES = List.of(
            new Case("", "Int", "List<Int>", "List.map(x -> x + x + 1, xs)", "[]"),
            new Case("", "Int", "Int", "List.fold((acc, x) -> acc + x, 0, xs)", "0"),
            new Case("", "Decimal", "Decimal", "List.fold((acc, x) -> acc + x, 0.0m, xs)", "0.0m"),
            new Case("", "String", "Int", "List.length(xs)", "0"),
            new Case("", "String", "String", "String.concat(xs)", "\"\""),
            new Case("", "List<Int>", "Int", "List.length(xs)", "0"),
            new Case("", "Bool", "Int", "List.length(xs)", "0"),
            new Case("", "Date", "Int", "List.length(xs)", "0"),
            new Case("""
                    data Pin = Int
                        invariant value >= 1 && value <= 12
                    """, "Pin", "Int", "List.length(xs)", "0"),
            new Case("""
                    data Request = { on: Date, count: Int }
                    """, "Request", "Int", "List.length(xs)", "0"));

    /** Each model is compiled once and asked both what {@code --generate} offers and what the
     *  verdict is, and every element that fails either is named. */
    @Test
    void generateOffersARowHoldingTheElementAndTheVerdictIsNotSatisfied() {
        List<String> failed = new ArrayList<>();
        for (Case each : BODIES) {
            Compilation compilation = compiled(each, each.body());
            List<RowsOfABlock.Row> rows = rowsForTheRewrite(offered(compilation));
            if (rows.size() != 1 || rows.getFirst().written().contains("([]) ->")) {
                failed.add(each.element() + " is offered " + rows);
            }
            AdequacyReport.AdequacyStatus status = AdequacyReport.of(compilation).adequacy();
            if (status != AdequacyReport.AdequacyStatus.NOT_SATISFIED) {
                failed.add(each.element() + " is " + status);
            }
        }
        assertEquals(List.of(), failed);
    }

    @Test
    void aBodyNoListTellsFromTheConstantIsOfferedNoRow() {
        Case constant = new Case("", "Int", "List<Int>", "[]", "[]");

        assertEquals(List.of(), rowsForTheRewrite(offered(compiled(constant, constant.body()))));
    }

    private static String offered(Compilation compilation) {
        return GeneratedRows.of(Adequacy.offeredFor(compilation.db(),
                        OfferingRequest.overTheModule("repro.nocallee")),
                Map.of(), SourceRendering.namedByIdentity(compilation.texts()),
                compilation.db()).text();
    }

    private static List<RowsOfABlock.Row> rowsForTheRewrite(String block) {
        return RowsOfABlock.of(block).stream()
                .filter(row -> row.behavior().equals("f"))
                .filter(row -> row.name().filter(ABodyThatCallsNoBehaviorIsOfferedAListOfOneElementTest::forTheRewrite).isPresent()
                        || row.fills().stream().anyMatch(
                                ABodyThatCallsNoBehaviorIsOfferedAListOfOneElementTest::forTheRewrite))
                .toList();
    }

    /** The row is for the body answering one value, whether named so or said so over it. */
    private static boolean forTheRewrite(String said) {
        return said.startsWith("the body answering what f");
    }

    private static Compilation compiled(Case each, String body) {
        Compilation compilation = Compilation.ofSource(MODEL.formatted(each.declarations(),
                each.element(), each.result(), body, each.answeredAtNone()), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(e -> e.diagnostic().code().toString()).toList(),
                () -> each + " compiles");
        return compilation;
    }
}
