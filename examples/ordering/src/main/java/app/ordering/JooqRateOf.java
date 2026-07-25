package app.ordering;

import example.tax.RateOf;
import example.tax.TaxCategory;
import example.tax.TaxRate;

import org.jooq.DSLContext;

import java.math.BigDecimal;
import java.util.Map;

import static org.jooq.impl.DSL.field;
import static org.jooq.impl.DSL.name;
import static org.jooq.impl.DSL.table;

/**
 * {@code rateOf}: the rate in force for a category, read from {@code tax_rates}. This is the only
 * place in the project where a NUMERIC column becomes a domain value — everything else in the schema
 * is INT (yen) or VARCHAR.
 *
 * <p>The category is turned into its stored key through its own encoder, so the tag written in the
 * table is the case name the discriminated codec uses, not a second spelling maintained by hand.
 *
 * <p>The rate is built through the protected factory the behavior inherits (it declares
 * {@code constructs TaxRate}), which runs the newtype's invariant. A row outside 0..1 is not a
 * business case — nothing in the domain can act on it — so it aborts, and the boundary maps that to
 * 500 like any other platform failure. A missing row is the same kind of thing: the model has no
 * "unknown rate" case, because a category always has a rate.
 */
public final class JooqRateOf extends RateOf {

    private final DSLContext dsl;

    public JooqRateOf(DSLContext dsl) {
        this.dsl = dsl;
    }

    @Override
    public TaxRate apply(TaxCategory category) {
        Map<String, Object> encoded = TaxCategory.encoder().encode(category);
        String key = (String) encoded.get("type");

        BigDecimal rate = dsl.select(field(name("rate"), BigDecimal.class))
                .from(table(name("tax_rates")))
                .where(field(name("category"), String.class).eq(key))
                .fetchOne(field(name("rate"), BigDecimal.class));

        if (rate == null) {
            throw new IllegalStateException("no tax rate configured for " + key);
        }
        return TaxRate(rate);
    }
}
