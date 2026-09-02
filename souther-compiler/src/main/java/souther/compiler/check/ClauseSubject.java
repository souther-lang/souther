package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.types.ValueName;

import java.util.function.Predicate;

/**
 * Which number of a value one conjunct of its rules is written about, with the comparison read so
 * that number is on the left.
 *
 * <p>Above the reading of ends, and not a step of it. What a rule is about and where it leaves the
 * values are two questions with two answers: {@code String.length(value) /= 0} is about the length
 * and places no end, and {@code String.length(value) == 5} is about the length and places both at
 * once. Read off the end, both of them are rules about nothing — and everything that decides which
 * number a position is measured on, what its values run between, and which rule drew an edge is
 * then short of them.
 *
 * <p>Nothing about the other side comes into it. A rule is about the number it names whether or not
 * what it stands against is something this compiler can fold: what the other side holds decides
 * where an end lands, and decides nothing about what the rule is about.
 *
 * <p>The comparison is handed back turned, so that the number this recognised is the side the claim
 * is stated of. A reader turning it again would be recognising the subject a second time to find
 * out which way round it already is.
 *
 * @param number     the number of the value the conjunct is written about
 * @param comparison the conjunct as a comparison, with {@code number} on the left
 */
public record ClauseSubject(FieldDomains.CoordinateKind number, ClauseComparison comparison) {

    /** The one name a newtype's own clause has for the value it is written on. */
    private static final String VALUE = "value";

    public ClauseSubject {
        if (number == null || comparison == null) {
            throw new IllegalArgumentException("a subject is some number a comparison names");
        }
    }

    /**
     * What {@code clause} is written about, or null where it is about no number of the value.
     *
     * <p>The measure first and the value second, which is an order and not a preference: the two
     * shapes are disjoint — {@code String.length(value)} is an application and {@code value} is a
     * name — so the order settles nothing, and asking in one is what keeps a second reader from
     * settling it differently.
     *
     * @param measure the operation a number of the value is taken by, or null for a caller asking
     *                only about the value itself
     */
    public static ClauseSubject of(Hir.Expr clause, ValueName measure) {
        ClauseComparison read = ClauseComparison.of(clause).orElse(null);
        if (read == null) {
            return null;
        }
        if (measure != null) {
            ClauseComparison taken = onTheLeft(read, e -> takesSizeOf(e, measure));
            if (taken != null) {
                return new ClauseSubject(
                        new FieldDomains.CoordinateKind.OfWhatAnOperationAnswers(measure), taken);
            }
        }
        ClauseComparison own = onTheLeft(read, ClauseSubject::isValue);
        return own == null ? null
                : new ClauseSubject(new FieldDomains.CoordinateKind.OfItsOwnValue(), own);
    }

    /** {@code read} with the side {@code is} recognises on the left, or null where neither side is
     *  one. */
    private static ClauseComparison onTheLeft(ClauseComparison read, Predicate<Hir.Expr> is) {
        if (is.test(read.left())) {
            return read;
        }
        ClauseComparison turned = read.turned();
        return is.test(turned.left()) ? turned : null;
    }

    private static boolean isValue(Hir.Expr e) {
        return e instanceof Hir.Var v && v.name().equals(VALUE);
    }

    /**
     * Whether {@code e} is {@code measure} applied to the value the clause is written on.
     *
     * <p>Asked of the name the application resolved to, not of how it was spelled: an import lets a
     * library operation be written without its qualifier, and a reader comparing text would miss
     * every clause written that way while looking as though it had read them.
     */
    private static boolean takesSizeOf(Hir.Expr e, ValueName measure) {
        return e instanceof Hir.Apply call && call.args().size() == 1
                && call.args().get(0) instanceof Hir.Var arg && arg.name().equals(VALUE)
                && call.function() instanceof Hir.Var.Denoting fn && measure.equals(fn.denotes());
    }
}
