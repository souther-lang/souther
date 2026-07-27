package example.invoicing;

import shared.money.Amount;
import shared.money.Currency;

import net.unit8.raoh.Err;
import net.unit8.raoh.Ok;
import net.unit8.raoh.Path;
import net.unit8.raoh.Result;

import org.junit.jupiter.api.Test;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * このプロジェクトは shared.money の .sou を持たない。型は sharedmoney の jar から来ていて、その
 * 宣言は jar のクラスに載っている。invariant を走らせているのも sharedmoney がビルドしたコードで、
 * ここで inline されたものではない。
 */
class CrossProjectImportTest {

    @Test
    void 別プロジェクトの型を自分のdataのフィールドに持てる() {
        Result<Invoice> decoded = Invoice.decoder().decode(
                Map.of("currency", "JPY",
                        "line", Map.of("description", "consulting", "amount", 1200L)),
                Path.ROOT);

        assertInstanceOf(Ok.class, decoded);
        assertEquals(1200L, value(decoded).line().amount().value());
    }

    @Test
    void 別プロジェクトが宣言したinvariantがここでも効く() {
        assertInstanceOf(Err.class, Amount.decoder().decode(-1L, Path.ROOT));
        assertInstanceOf(Err.class, Currency.decoder().decode("JPYEN", Path.ROOT));
    }

    @Test
    void 別プロジェクトの型を受け取るbehaviorを呼べる() {
        Line line = value(Line.decoder().decode(
                Map.of("description", "consulting", "amount", 1200L), Path.ROOT));
        Currency jpy = value(Currency.decoder().decode("JPY", Path.ROOT));

        Invoice invoice = Issue.of().apply(line, jpy);

        assertEquals("consulting", invoice.line().description());
        assertEquals(1200L, invoice.line().amount().value());
    }

    private static <T> T value(Result<T> result) {
        return switch (result) {
            case Ok<T>(var v) -> v;
            case Err<T> e -> throw new AssertionError(e.issues().asList().toString());
        };
    }
}
