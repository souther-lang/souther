package app.ordering;

import example.cart.PricedCart;
import example.tax.TaxBreakdown;
import example.tax.TaxCategory;
import example.tax.TaxFor;
import example.tax.TaxRate;

import net.unit8.raoh.Err;
import net.unit8.raoh.Ok;
import net.unit8.raoh.Path;
import net.unit8.raoh.Result;

import org.jooq.DSLContext;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.Test;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.boot.test.context.SpringBootTest;

import java.math.BigDecimal;
import java.util.List;
import java.util.Map;

import static org.jooq.impl.DSL.field;
import static org.jooq.impl.DSL.name;
import static org.jooq.impl.DSL.table;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * The tax rate comes from H2, through jOOQ, as the schema's one NUMERIC column — the only place in
 * this project where a database value becomes a {@code Decimal} rather than an {@code Int} or a
 * {@code String}. Boot starts for real ({@code @SpringBootTest}) and the bound {@code taxFor} runs
 * against the seeded rows.
 *
 * <p>The arithmetic itself is fixed by tax.sou's {@code example}s with the lookup faked; what is
 * checked here is the path the fake stands in for.
 */
@SpringBootTest
class TaxRateFromDatabaseTest {

    @Autowired TaxFor taxFor;
    @Autowired DSLContext dsl;

    @AfterEach
    void restoreRates() {
        setRate("StandardRate", "0.100");
        setRate("ReducedRate", "0.080");
    }

    private void setRate(String category, String rate) {
        dsl.mergeInto(table(name("tax_rates")))
                .columns(field(name("category")), field(name("rate")))
                .key(field(name("category")))
                .values(category, new BigDecimal(rate))
                .execute();
    }

    /** A category is decoded, not constructed: nothing outside the generated code can build one. */
    private TaxCategory category(String tag) {
        return ok(TaxCategory.decoder().decode(Map.of("type", tag), Path.ROOT));
    }

    private <T> T ok(Result<T> r) {
        if (r instanceof Err<T> e) {
            throw new AssertionError("should decode: " + e.issues().asList());
        }
        return ((Ok<T>) r).value();
    }

    private PricedCart cart(long total) {
        return ok(PricedCart.decoder().decode(Map.of(
                "items", List.of(Map.of("sku", "apple", "quantity", 3L, "unitPrice", 105L, "weightGrams", 120L)),
                "total", total,
                "highValue", false), Path.ROOT));
    }

    @Test
    void theRateIsReadFromTheNumericColumn() {
        TaxBreakdown standard = taxFor.apply(cart(315L), category("StandardRate"));
        assertEquals(0, new BigDecimal("0.100").compareTo(standard.rate().value()));
        assertEquals(31L, standard.tax(), "315 × 0.100 = 31.5, dropped to 31");
        assertEquals(346L, standard.gross());

        TaxBreakdown reduced = taxFor.apply(cart(1100L), category("ReducedRate"));
        assertEquals(0, new BigDecimal("0.080").compareTo(reduced.rate().value()));
        assertEquals(88L, reduced.tax());
    }

    @Test
    void aRevisedRateChangesTheAnswerWithoutTouchingTheModel() {
        // What the column is for: the figure is administered outside the domain.
        setRate("StandardRate", "0.120");

        TaxBreakdown after = taxFor.apply(cart(315L), category("StandardRate"));
        assertEquals(37L, after.tax(), "315 × 0.120 = 37.8, dropped to 37");
    }

    @Test
    void aRowOutsideTheRateRangeAborts() {
        // The invariant runs where the value is built, so a bad row cannot enter the domain. It is
        // not a business case — nothing could act on it — so it aborts rather than returning a case.
        setRate("StandardRate", "1.500");

        assertThrows(souther.runtime.ConstraintViolation.class,
                () -> taxFor.apply(cart(315L), category("StandardRate")));
    }

    /** The rate a row carries is written for the invoice inside the domain, not reassembled at the
     *  boundary: 0.100 from the NUMERIC column becomes the string "10%". */
    @Test
    void theRateIsWrittenAsAPercentage() {
        assertEquals("10%", taxFor.apply(cart(315L), category("StandardRate")).rateLabel());

        // A rate the column states to three places still reads as whole percent — the rounding in
        // rateLabel decides how many places are shown, not the scale the row happened to carry.
        setRate("StandardRate", "0.080");
        assertEquals("8%", taxFor.apply(cart(315L), category("StandardRate")).rateLabel());
    }

    @Test
    void theDecimalRateStillRoundTripsThroughTheCodec() {
        TaxRate rate = taxFor.apply(cart(315L), category("StandardRate")).rate();
        assertEquals(0, new BigDecimal("0.100").compareTo(TaxRate.encoder().encode(rate)));
    }
}
