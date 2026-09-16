package souther.compiler.partition;

import souther.compiler.check.ComparisonClaim;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.Towards;

import java.math.BigDecimal;
import java.util.Map;

/**
 * A border read as one inequality over the positions it is drawn on.
 *
 * <p>What a rule that orders values says, with the shape it was written in gone: a direction over
 * the positions, a place along that direction where the values part, and which side of it the rule
 * is satisfied on. A bound on one position, a rule holding two positions apart and a rule over an
 * arithmetic form all read this way, because that is what {@link BorderQuantity#direction} answers
 * and it answers it for all three.
 *
 * <p><b>What this is for is holding a line against a line the model did not draw.</b> A border says
 * where a row has to stand to be at its own line; this says what the line <em>is</em>, in terms
 * another line can be written in — so a reader can ask which rows would answer differently if the
 * positions were weighed otherwise. Asked of a border, that question has nowhere to be put: a border
 * is one line together with what is owed at its points.
 *
 * <p>The direction with its common divisor taken out ({@link QuantityKey}), so that a rule and any
 * positive multiple of it are one boundary. How far along the direction the line falls is the seam's,
 * in the quantity's own units, and it is taken from the seam rather than divided back out of what
 * the rule wrote: {@code 3 * d <= 1} cuts at a third and no decimal this language writes is one.
 *
 * <p>Only a rule that orders the values either side of what it wrote. A rule that names a value
 * orders nothing and has no side to be satisfied on, so there is no such reading of it — said by
 * there being none ({@link #of}) rather than by an invented side.
 *
 * @param of          the quantity, which is what reads a row's positions and what names the line
 * @param seam        where the values part, in the quantity's own units
 * @param satisfiedOn the side of it the rule is satisfied on
 */
public record OrderedAffineBoundary(BorderQuantity of, Seam seam, Towards satisfiedOn) {

    public OrderedAffineBoundary {
        if (of == null || seam == null || satisfiedOn == null) {
            throw new IllegalArgumentException("a boundary is a quantity parted somewhere, with a"
                    + " side it is satisfied on: " + of + " " + seam + " " + satisfiedOn);
        }
    }

    /**
     * How {@code border} reads as one inequality, or null where its rule names a value rather than
     * ordering the values around it.
     *
     * <p>Derived from the border and held nowhere, so there is no second copy to disagree with the
     * one the rule was read to. Where the values part is asked of the one derivation of it
     * ({@link Seam#where}), which is what the reading that met the rule asked.
     */
    public static OrderedAffineBoundary of(Border border) {
        ComparisonClaim claim = border.origin().lineFacts().claim();
        BorderQuantity of = border.cut().of();
        if (!(claim instanceof ComparisonClaim.Cut order) || !weighable(of)) {
            return null;
        }
        return new OrderedAffineBoundary(of, Seam.where(of, border.cut().at(), claim),
                order.satisfyingSide());
    }

    /**
     * Whether this quantity's positions hold numbers a form could weigh.
     *
     * <p>Two strings stand one above the other and no distance apart, so a rule holding them apart
     * draws a line on an order with no numbers under it. Such a line has no weights to be written
     * differently — there is nothing to multiply — so it is not a boundary of this kind, and reading
     * one asks its positions for a number they do not have.
     */
    public static boolean weighable(BorderQuantity of) {
        for (NumericTerm term : of.terms()) {
            souther.compiler.check.Carrier on = of.carrierOf(term);
            if (on == null || !on.counts()) {
                return false;
            }
        }
        return true;
    }

    /** The quantity this is a boundary on, with its common divisor taken out. */
    public QuantityKey direction() {
        return QuantityKey.of(of.direction());
    }

    /**
     * The positions of it a rule could write another weight for.
     *
     * <p>Asked of each position's own order ({@link souther.compiler.check.Carrier#canBeWeighed}).
     * A date counts from an origin nobody wrote, so a line weighing one of them two is a line
     * nobody can state — and the weights such a position has are the one pair a distance is written
     * with.
     */
    public java.util.Set<NumericTerm> weighedByANumber() {
        return weighedByANumber(of);
    }

    /** The same, asked of a quantity rather than of a boundary on it — for a caller working out
     *  whether there is a boundary of this kind to build at all. */
    public static java.util.Set<NumericTerm> weighedByANumber(BorderQuantity of) {
        java.util.Set<NumericTerm> out = new java.util.LinkedHashSet<>();
        for (NumericTerm term : QuantityKey.of(of.direction()).direction().keySet()) {
            souther.compiler.check.Carrier on = of.carrierOf(term);
            if (on != null && on.canBeWeighed()) {
                out.add(term);
            }
        }
        return out;
    }

    /**
     * Whether a row whose positions read as {@code values} satisfies the rule that drew this.
     *
     * <p>Asked of the numbers rather than of the row, so that the same question can be put to a
     * direction nobody wrote. Where a row's value falls is the seam's answer and which side satisfies
     * is the rule's, and the two are held apart here for the reason they are held apart everywhere:
     * {@code n <= 100} and {@code n > 100} part the values in one place and are satisfied on
     * opposite sides of it.
     */
    public boolean satisfiedBy(Map<NumericTerm, Place> values) {
        return seam.sideOf(new Count(along(direction().direction(), values))) == satisfiedOn;
    }

    /**
     * What a direction comes to at a row, which is what each position holds weighed by what the
     * direction weighs it.
     *
     * <p>Zero for a position the direction does not name, which is what a coefficient of nothing is.
     * Written here for both the line the model drew and the lines it did not, so that neither is
     * scored by a rule the other is not.
     */
    public static BigDecimal along(Map<NumericTerm, BigDecimal> direction,
                                   Map<NumericTerm, Place> values) {
        BigDecimal at = BigDecimal.ZERO;
        for (Map.Entry<NumericTerm, BigDecimal> each : direction.entrySet()) {
            Place held = values.get(each.getKey());
            if (held == null) {
                throw new IllegalArgumentException("a row read at a quantity holds a number at each"
                        + " of its positions, and holds none at " + each.getKey());
            }
            at = at.add(Count.number(held).at().multiply(each.getValue()));
        }
        return at;
    }

    /** The left of the {@code left = right} a report names this line by, which is the quantity's
     *  own word for itself. */
    public String left() {
        return of.left();
    }

    /**
     * How an input of a quantity's positions is written, each value on the order its position is
     * read on.
     *
     * <p>Written by the carrier and not as the number the arithmetic came to. A position read as a
     * date counts its days from somewhere, and a reader handed the count has been handed a number
     * that is not what they would write in a row.
     */
    public static String saidAt(BorderQuantity of, Map<NumericTerm, Place> values) {
        StringBuilder out = new StringBuilder();
        // In the order the quantity's own form is spelled in, so that an input and the line it is
        // an input of name their positions the same way round. Taken in the order the terms were
        // recorded, a reader compares a form written one way against a row written another.
        for (Map.Entry<NumericTerm, java.math.BigDecimal> each
                : AffineReading.ordered(of.direction())) {
            NumericTerm term = each.getKey();
            Place at = values.get(term);
            souther.compiler.check.Carrier on = of.carrierOf(term);
            if (at == null || on == null) {
                return null;
            }
            out.append(out.isEmpty() ? "" : ", ").append(term).append(" = ").append(on.written(at));
        }
        return out.isEmpty() ? null : out.toString();
    }

    /**
     * How a direction is written as an author would write the form.
     *
     * <p>One spelling, for the form a rule wrote and for a form nobody wrote alike. A report that
     * names a line the model did not draw writes it beside the one it did, and two renderings would
     * have the pair a reader is comparing spelled two ways.
     */
    public static String spelled(Map<NumericTerm, BigDecimal> direction) {
        StringBuilder out = new StringBuilder();
        for (Map.Entry<NumericTerm, BigDecimal> each
                : AffineReading.ordered(new LinearForm<>(BigDecimal.ZERO, direction))) {
            BigDecimal coef = each.getValue();
            if (out.isEmpty()) {
                out.append(coef.signum() < 0 ? "-" : "");
            } else {
                out.append(coef.signum() < 0 ? " - " : " + ");
            }
            BigDecimal size = coef.abs();
            if (size.compareTo(BigDecimal.ONE) != 0) {
                out.append(size.stripTrailingZeros().toPlainString()).append(" * ");
            }
            out.append(each.getKey());
        }
        return out.toString();
    }
}
