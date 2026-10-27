package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.meta.ModulePath;
import souther.compiler.observe.AnswerObservation;
import souther.compiler.observe.RowOutcome;
import souther.compiler.observe.Stage;
import souther.compiler.report.GeneratedRows;
import souther.compiler.source.SourceId;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * A row offered for a quote whose lines define their net is a quote: it satisfies the line's rule,
 * the list's rules and the quote's own, and the behavior answers it.
 *
 * <p>The rows are the ones offered at the boundary of the comparison the quote's total is held
 * against, written out and run as a person who pastes them would run them. A row that broke one of
 * the rules is refused before the body is applied, and does not answer.
 */
class ARowOfferedBesideLinesThatDefineTheirNetRunsTest {

    private static final String MODEL = """
            module demo

            data Amount = Decimal
                invariant value >= 0.0m
            data Quantity = Int
                invariant value >= 1
            data UnitPrice = Decimal
                invariant value >= 0.0m
            data DiscountRate = Decimal
                invariant value >= 0.0m && value <= 0.5m
            data ProductCode = String
                invariant String.matches("[A-Z]{2}-[0-9]{4}", value)

            data Line =
                { product: ProductCode
                , quantity: Quantity
                , listPrice: UnitPrice
                , discount: DiscountRate
                , net: Amount
                }
                invariant Decimal.compare(net.value,
                    Decimal.round(2, HALF_UP, Decimal.fromInt(quantity.value) * listPrice.value
                                  * (1.0m - discount.value))) == 0

            data Lines = List<Line>
                invariant nonEmpty = List.length(value) >= 1
                invariant uniqueProducts = List.allDistinctBy(.product, value)

            data Quote = { lines: Lines, subtotal: Amount, total: Amount }
                invariant Decimal.compare(total.value, subtotal.value) <= 0

            data Ok
            data Over = { by: Amount }

            behavior probe : (q: Quote) -> Ok | Over
                constructs Over
            let probe (q) =
                if Decimal.compare(q.total.value, 100.0m) > 0 then Over { by = q.total } else Ok
            """;

    @Test
    void everyRowOfferedIsAQuoteTheBehaviorAnswers() {
        Compilation compilation = Compilation.ofSources(List.of(MODEL), ModulePath.EMPTY);
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        StringBuilder offered = new StringBuilder();
        for (String module : compilation.modules()) {
            offered.append(GeneratedRows.of(
                    Adequacy.offeredFor(compilation.db(), OfferingRequest.overTheModule(module)),
                    Map.of(), SourceRendering.namedByIdentity(compilation.texts()),
                    compilation.db()).text());
        }
        assertFalse(offered.isEmpty(), "rows are offered for the comparison against the total");

        Compilation pasted =
                Compilation.ofSources(List.of(MODEL + "\n" + offered), ModulePath.EMPTY);
        List<RowOutcome> rows = new ArrayList<>();
        for (String module : pasted.modules()) {
            for (SourceId id : pasted.exampleSourcesOf(module)) {
                Output.Examples.Of ran = pasted.db()
                        .ask(Output.Examples.asked(pasted.db(), module, id)).value();
                if (ran != null) {
                    rows.addAll(ran.rows());
                }
            }
        }
        assertFalse(rows.isEmpty(), "the offered rows are examples of the behavior");
        for (RowOutcome row : rows) {
            assertEquals(Stage.ANSWERED, row.stage(), "a row offered is a quote: " + row);
            assertInstanceOf(AnswerObservation.Answered.class, row.answer());
        }
    }
}
