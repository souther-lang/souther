package souther.compiler.partition;

import souther.compiler.ast.Ast;
import souther.compiler.check.InvariantBound;

import java.math.BigDecimal;
import java.util.function.Function;

/**
 * The value a rule is written against, read on the carrier the rule's position is on.
 *
 * <p>One reader for one carrier. Which literals a rule may be bounded by is decided by what carries
 * the value — a date is written as a date wherever it is written — and it was being decided
 * separately by each reader that wanted one, so an invariant and a {@code guard} at the same
 * position admitted different rules and only one of them said so.
 *
 * <p>Every number that leaves here is a count on {@link Carrier}, never a value a person writes.
 * What turns one back is {@link Dates} and the fixture templates, so a bound, a cut and a generated
 * row cannot disagree about which date a line is drawn at.
 */
final class OrderedLiteral {

    /** How a bound written in an invariant is read on {@code carrier}. */
    static Function<Ast.Expr, BigDecimal> on(Carrier carrier) {
        return switch (carrier) {
            case WHOLE -> InvariantBound::wholeLiteral;
            case DENSE -> InvariantBound::literalOf;
            case DATE -> e -> temporal(e, "Date", Dates::dayOf);
            case MOMENT -> e -> temporal(e, "DateTime", DateTimes::secondOf);
        };
    }

    /** The count a written temporal is, or null where the expression is not one of that kind. A
     *  temporal is written as a literal with its text spelled out (spec
     *  §a-temporal-value-is-written-as-a-literal), so it is read here rather than run. */
    private static BigDecimal temporal(Ast.Expr e, String written,
                                       Function<String, BigDecimal> countOf) {
        return e instanceof Ast.Apply call && written.equals(call.reaches())
                && call.args().size() == 1 && call.args().get(0) instanceof Ast.StringLit iso
                ? countOf.apply(iso.value()) : null;
    }

    private OrderedLiteral() {}
}
