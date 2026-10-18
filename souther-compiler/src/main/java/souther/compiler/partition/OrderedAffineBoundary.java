package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.check.ComparisonClaim;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.NumericTerms;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.Towards;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * A border read as one inequality over the positions it is drawn on.
 *
 * <p>What a rule that orders values says, with the shape it was written in gone: a direction over
 * the positions, a place along that direction where the values part, and which side of it the rule
 * is satisfied on. A bound on one position, a rule holding two positions apart and a rule over an
 * arithmetic form all read this way, because that is what {@link LinearQuantity#direction} answers
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
 * @param direction   the quantity with its common divisor taken out. Worked out once, with the
 *                    boundary, since every row a line is weighed at is read along it
 */
public record OrderedAffineBoundary(LinearQuantity of, Seam seam, Towards satisfiedOn,
                                    QuantityKey direction) {

    public OrderedAffineBoundary {
        if (of == null || seam == null || satisfiedOn == null || direction == null) {
            throw new IllegalArgumentException("a boundary is a quantity parted somewhere, with a"
                    + " side it is satisfied on: " + of + " " + seam + " " + satisfiedOn);
        }
        if (!direction.equals(QuantityKey.of(of.direction()))) {
            throw new IllegalArgumentException("a boundary runs the way its quantity does: "
                    + direction + " for " + of);
        }
    }

    /** The boundary on {@code of}, running the way {@code of} does. */
    public OrderedAffineBoundary(LinearQuantity of, Seam seam, Towards satisfiedOn) {
        this(of, seam, satisfiedOn, QuantityKey.of(of.direction()));
    }

    /**
     * How {@code border} reads as one inequality, empty where its rule names a value rather than
     * ordering the values around it, and unheld where the values beside its line were not worked
     * out.
     *
     * <p>Derived from the border and held nowhere, so there is no second copy to disagree with the
     * one the rule was read to. Where the values part is asked of the one derivation of it
     * ({@link Seam#where}), which is what the reading that met the rule asked.
     */
    public static ExactAnswer<Optional<OrderedAffineBoundary>> of(Border border) {
        ComparisonClaim claim = border.origin().lineFacts().claim();
        if (!(claim instanceof ComparisonClaim.Cut order)
                || !(border.cut().of() instanceof LinearQuantity of) || !weighable(of)) {
            return ExactAnswer.held(Optional.empty());
        }
        return Seam.where(of, border.cut().at(), claim).map(seam ->
                Optional.of(new OrderedAffineBoundary(of, seam, order.satisfyingSide())));
    }

    /**
     * Whether this quantity's positions hold numbers a form could weigh.
     *
     * <p>Two strings stand one above the other and no distance apart, so a rule holding them apart
     * draws a line on an order with no numbers under it. Such a line has no weights to be written
     * differently — there is nothing to multiply — so it is not a boundary of this kind, and reading
     * one asks its positions for a number they do not have.
     */
    public static boolean weighable(LinearQuantity of) {
        for (NumericTerm term : of.terms()) {
            Carrier on = of.carrierOf(term);
            if (on == null || !on.counts()) {
                return false;
            }
        }
        return true;
    }

    /**
     * The positions of a quantity a rule could write another weight for — for a caller working out
     * whether there is a boundary of this kind to build at all.
     *
     * <p>Asked of each position's own order ({@link Carrier#canBeWeighed}).
     * A date counts from an origin nobody wrote, so a line weighing one of them two is a line
     * nobody can state — and the weights such a position has are the one pair a distance is written
     * with.
     */
    public static Set<NumericTerm> weighedByANumber(LinearQuantity of) {
        Set<NumericTerm> out = new LinkedHashSet<>();
        // A linked set answers in the order it was filled, so it is filled in the order the
        // direction holds its terms in, which is theirs.
        for (NumericTerm term : QuantityKey.of(of.direction()).direction().keySet()) {
            Carrier on = of.carrierOf(term);
            if (on != null && on.canBeWeighed()) {
                out.add(term);
            }
        }
        return out;
    }

    /**
     * Whether a row whose positions read as {@code values} satisfies the rule that drew this, or why
     * its sum could not be worked out.
     *
     * <p>Asked of the numbers rather than of the row, so that the same question can be put to a
     * direction nobody wrote. Where a row's value falls is the seam's answer and which side satisfies
     * is the rule's, and the two are held apart here for the reason they are held apart everywhere:
     * {@code n <= 100} and {@code n > 100} part the values in one place and are satisfied on
     * opposite sides of it.
     */
    public ExactAnswer<Boolean> satisfies(Map<NumericTerm, Place> values) {
        // Three answers and not two. A row whose sum the exact arithmetic cannot hold is neither
        // kept nor refused as far as this can tell, and read as either it is evidence nobody
        // established: read as refused, a row the model keeps would rule out a line beside this one.
        return along(direction, values).map(at -> seam.sideOf(at) == satisfiedOn);
    }

    /**
     * What a direction comes to at a row, which is what each position holds weighed by what the
     * direction weighs it — or which way the exact arithmetic could not hold the sum.
     *
     * <p>Zero for a position the direction does not name, which is what a coefficient of nothing is.
     * Written here for both the line the model drew and the lines it did not, so that neither is
     * scored by a rule the other is not.
     *
     * <p>Walked in the order the direction holds its terms in, which is put in place where the
     * direction is made and not again for each row.
     */
    public static ExactAnswer<ExactRatio> along(QuantityKey direction,
                                                Map<NumericTerm, Place> values) {
        return summed(direction.direction().keySet(), direction.direction(), values,
                ExactRatio.ZERO);
    }

    /**
     * What {@code form} comes to at a row: its constant and what each position holds weighed by its
     * coefficient, as one sum — or which way the exact arithmetic could not hold it.
     */
    public static ExactAnswer<ExactRatio> at(LinearForm<NumericTerm> form,
                                             Map<NumericTerm, Place> values) {
        return summed(form.coefs(), values, form.constant());
    }

    /**
     * What {@code dividend} leaves by {@code divisor} at a row: the form there, less every whole
     * turn of the divisor — none where the form does not come to a whole number, which leaves no
     * remainder — or which way the exact arithmetic could not hold the form.
     *
     * <p>The one place a remainder of a form is worked out of the numbers a row holds, so a row
     * read against a border on it and a value of a position read for what it comes to are read
     * alike.
     */
    static ExactAnswer<Optional<ExactRatio>> remainderAt(LinearForm<NumericTerm> dividend,
                                                         BigInteger divisor,
                                                         Map<NumericTerm, Place> values) {
        return at(dividend, values).map(comesTo -> comesTo.isWhole()
                && comesTo.floor() instanceof ExactAnswer.Held<BigInteger> whole
                ? Optional.of(ExactRatio.of(whole.value().mod(divisor))) : Optional.empty());
    }

    /**
     * What {@code dividend} leaves by {@code divisor} at a row, both whole numbers: the dividend
     * less every whole turn of the divisor, taking the divisor's sign — none where the divisor is
     * nought, which stops the run before a remainder is worked out — or which way the exact
     * arithmetic could not hold either number.
     *
     * <p>The one place a remainder by an input's number is worked out of the numbers a row holds,
     * so a row read against a border on it, a value read for what it comes to and a row a search
     * composed are read alike. Both numbers are values of their type, and the remainder of two
     * values of a type lies between them and nought, so it is one too.
     */
    static ExactAnswer<Optional<ExactRatio>> remainderByAnInputAt(NumericTerm dividend,
            NumericTerm divisor, Map<NumericTerm, Place> values) {
        ExactRatio number = Count.number(values.get(dividend)).exactly();
        ExactRatio by = Count.number(values.get(divisor)).exactly();
        if (!number.isWhole() || !by.isWhole()
                || !(number.floor() instanceof ExactAnswer.Held<BigInteger>(BigInteger whole))
                || !(by.floor() instanceof ExactAnswer.Held<BigInteger>(BigInteger turn))) {
            return ExactAnswer.held(Optional.empty());
        }
        if (turn.signum() == 0) {
            return ExactAnswer.held(Optional.empty());
        }
        // The remainder by the divisor's size, moved down to the divisor's side where it has one.
        BigInteger left = whole.mod(turn.abs());
        return ExactAnswer.held(Optional.of(ExactRatio.of(
                turn.signum() < 0 && left.signum() != 0 ? left.add(turn) : left)));
    }

    /**
     * What the two whole numbers {@code factors} come to multiplied at a row — none where the
     * product passes where their type stops — or which way the exact arithmetic could not hold it.
     *
     * <p>The one place a product of two numbers is worked out of the numbers a row holds, so a row
     * read against a border on it, a value read for what it comes to and a row a search composed
     * are read alike. The run multiplies the two in their type and stops where the product is
     * past its ends, so such a row has no product at all, and stands on neither side of a line on
     * it: none is that, which the exact arithmetic failing to hold a number is not.
     */
    static ExactAnswer<Optional<ExactRatio>> productAt(List<NumericTerm> factors,
                                                       Map<NumericTerm, Place> values) {
        return Count.number(values.get(factors.get(0))).exactly()
                .times(Count.number(values.get(factors.get(1))).exactly())
                .map(product -> product.floor() instanceof ExactAnswer.Held<BigInteger>(
                        BigInteger whole)
                        && Carrier.WHOLE.extent().admits(Count.of(new BigDecimal(whole)))
                        ? Optional.of(product) : Optional.empty());
    }

    /**
     * {@code constant} and each weighed number, added as one sum ({@link ExactRatio#sum}), so
     * whether it is held does not turn on which term came first.
     */
    private static ExactAnswer<ExactRatio> summed(Map<NumericTerm, ExactRatio> direction,
                                                  Map<NumericTerm, Place> values,
                                                  ExactRatio constant) {
        // Walked by the terms: which position is named where a row holds no number at one of them
        // turns on the order, and a direction says which positions it weighs without saying which
        // was written first.
        return summed(NumericTerms.inOrder(direction.keySet()), direction, values, constant);
    }

    /**
     * What {@code of} with {@code constant} added comes to at a row, walked in the order its terms
     * are held in rather than put in order again for every row.
     */
    static ExactAnswer<ExactRatio> at(LinearQuantity of, ExactRatio constant,
                                      Map<NumericTerm, Place> values) {
        return summed(of.terms(), of.direction().coefs(), values, constant);
    }

    private static ExactAnswer<ExactRatio> summed(Collection<NumericTerm> walked,
                                                  Map<NumericTerm, ExactRatio> direction,
                                                  Map<NumericTerm, Place> values,
                                                  ExactRatio constant) {
        List<ExactRatio> terms = new ArrayList<>();
        terms.add(constant);
        for (NumericTerm term : walked) {
            Place held = values.get(term);
            if (held == null) {
                throw new IllegalArgumentException("a row read at a quantity holds a number at each"
                        + " of its positions, and holds none at " + term);
            }
            switch (Count.number(held).exactly().times(direction.get(term))) {
                case ExactAnswer.Held<ExactRatio> weighed -> terms.add(weighed.value());
                case ExactAnswer.Unheld<ExactRatio> unheld -> {
                    return ExactAnswer.unheld(unheld.why());
                }
            }
        }
        return ExactRatio.sum(terms);
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
    public static String saidAt(BorderQuantity quantity, Map<NumericTerm, Place> values) {
        // An input is said position by position, and a quantity that is no form over positions
        // has none to say it by.
        if (!(quantity instanceof LinearQuantity of)) {
            return null;
        }
        StringBuilder out = new StringBuilder();
        // In the order the quantity's own form is spelled in, so that an input and the line it is
        // an input of name their positions the same way round. Taken in the order the terms were
        // recorded, a reader compares a form written one way against a row written another.
        for (Map.Entry<NumericTerm, ExactRatio> each
                : AffineReading.ordered(of.direction())) {
            NumericTerm term = each.getKey();
            Place at = values.get(term);
            Carrier on = of.carrierOf(term);
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
    public static String spelled(Map<NumericTerm, ExactRatio> direction) {
        StringBuilder out = new StringBuilder();
        for (Map.Entry<NumericTerm, ExactRatio> each
                : AffineReading.ordered(new LinearForm<>(ExactRatio.ZERO, direction))) {
            ExactRatio coef = each.getValue();
            if (out.isEmpty()) {
                out.append(coef.signum() < 0 ? "-" : "");
            } else {
                out.append(coef.signum() < 0 ? " - " : " + ");
            }
            ExactRatio size = coef.abs();
            if (!size.equals(ExactRatio.ONE)) {
                out.append(size.spelled()).append(" * ");
            }
            out.append(each.getKey());
        }
        return out.toString();
    }
}
