package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.check.ComparisonClaim;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.NumericDomain.LinearForm;

/**
 * What one comparison cuts, and where — the one place that decides it.
 *
 * <p><b>One decision, so that a rule is read the same way wherever it is written.</b> Which quantity
 * a comparison cuts was settled in three places, each reading a little more of the language than the
 * last and each turning the form round or not on its own: a rule written {@code 48 >= 3a + 6b} drew
 * its border on {@code -3a - 6b}, and the {@code ensures} side called two of the three readings and
 * so read no form at all. That is the shape this whole reading was written to stop, one level up
 * from where it was found.
 *
 * <p>Three readings, in this order, and the order is not a preference. The first two read carriers
 * whose values the arithmetic cannot: a date against a written date, a case of an enumeration, one
 * string against another. The third reads the arithmetic, which reaches every carrier that counts
 * and no other. So a comparison is met by whichever of them can say what it states, and all three
 * answer the same question — the canonical form decides the variant, and a reading that stops
 * earlier stops because the arithmetic has no numbers there rather than because of how the rule was
 * spelled.
 *
 * @param of     what the rule cuts
 * @param at     where on it
 * @param claim  what the operator states about the threshold's own value
 * @param within what the rules leave the quantity itself, or null where they leave it everything.
 *               A form's own values are bounded by what its positions are bounded by — three times
 *               a length is never negative — and a threshold outside them is one the rule draws no
 *               border at
 */
record Cutting(BorderQuantity of, Level at, ComparisonClaim claim,
               souther.compiler.numeric.NumericDomain.Bounds within) {

    /** The line {@code comparison} draws, or null where nothing here reads one. */
    static Cutting of(String behavior, Core.Binary comparison, InputReads reads, Symbols symbols) {
        // Read once and handed to each of the three. Each reading asks the same arithmetic a
        // different question, and walking the comparison again per question is four to six walks of
        // every comparison in every body and every clause.
        AffineReading read = AffineReading.of(comparison, reads, symbols);
        ComparedLine atAPosition = ComparedLine.of(comparison, read, reads, symbols);
        if (atAPosition != null) {
            return new Cutting(
                    new BorderQuantity.OfACoordinate(AxisId.of(behavior, atAPosition.term()),
                            atAPosition.term(), atAPosition.carrier()),
                    new Level.OnACarrier(atAPosition.carrier(), atAPosition.value()),
                    claimOf(atAPosition), null);
        }
        ComparedTerms apart = ComparedTerms.of(comparison, read, reads, symbols);
        if (apart != null) {
            return new Cutting(
                    new BorderQuantity.Apart(behavior, apart.on(), apart.against(), apart.carrier()),
                    new Level.ACount(apart.stepsApart()),
                    new ComparisonClaim.Cut(apart.valueBelongsBelow(), apart.holdsAtTheLine()),
                    null);
        }
        return overAForm(behavior, read, reads, symbols);
    }

    /**
     * The line an arithmetic form over several positions draws.
     *
     * <p>Read where neither of the narrower readings could be, and about the same comparison. This
     * is the case domain testing exists for — a partition defined by a condition over more than one
     * variable — and the four sides of the box its positions sit in are not it.
     *
     * <p>Only where every position of the form is counted on one order. A form adds its positions
     * together, and two orders whose counts mean different things have no sum: a day count and a
     * number are not addable, and a rule that looked addable because both sides type-checked would
     * put a border at a number nothing stands at.
     */
    private static Cutting overAForm(String behavior, AffineReading read, InputReads reads,
                                     Symbols symbols) {
        if (read == null || !read.orders()) {
            return null;
        }
        Carrier carrier = read.carrier(reads, symbols);
        if (carrier == null || !carrier.counts()) {
            return null;
        }
        return new Cutting(new BorderQuantity.OverAForm(behavior, read.form(), carrier),
                new Level.ACount(new Count(read.cut())), read.claim(), reachOf(read, reads));
    }

    /**
     * What the form's own values run between, from what its positions run between.
     *
     * <p>A quantity is bounded by what it is made of. Three times a length is never negative,
     * whatever a rule happens to compare it against — and a threshold outside what the form takes is
     * one no border is drawn at, rather than one whose points a search is sent looking for and never
     * finds.
     *
     * <p>Null where a position is unbounded either way, which leaves the form unbounded that way and
     * nothing to say.
     */
    private static souther.compiler.numeric.NumericDomain.Bounds reachOf(AffineReading read,
                                                                        InputReads reads) {
        java.util.Map<NumericTerm, souther.compiler.numeric.Rational> coefs =
                new java.util.LinkedHashMap<>();
        read.form().coefs().forEach((term, coef) ->
                coefs.put(term, souther.compiler.numeric.Rational.of(coef)));
        souther.compiler.numeric.Reach runs = souther.compiler.numeric.Reach.of(
                coefs, souther.compiler.numeric.Rational.ZERO,
                term -> runsBetween(term, reads));
        if (runs.least() == null || runs.most() == null) {
            return null;
        }
        return new souther.compiler.numeric.NumericDomain.Bounds(
                written(runs.least()), written(runs.most()));
    }

    /** A cut as the end of a range. Every end that reaches here came from a written number, so what
     *  it is written as is what it was. */
    private static souther.compiler.numeric.Endpoint written(
            souther.compiler.numeric.RationalCut cut) {
        java.math.BigDecimal at = cut.at().asWrittenDecimal();
        if (at == null) {
            throw new IllegalStateException("a quantity's reach is written: " + cut);
        }
        return new souther.compiler.numeric.Endpoint(
                new souther.compiler.numeric.Count(at), cut.inclusive());
    }

    /** What one position runs between, as the arithmetic wants it. */
    private static souther.compiler.numeric.Reach runsBetween(NumericTerm term, InputReads reads) {
        souther.compiler.numeric.NumericDomain.Bounds bounds = boundsOf(term, reads);
        if (bounds == null) {
            return souther.compiler.numeric.Reach.ANYWHERE;
        }
        return souther.compiler.numeric.Reach.between(asCut(bounds.min()), asCut(bounds.max()));
    }

    private static souther.compiler.numeric.RationalCut asCut(
            souther.compiler.numeric.Endpoint end) {
        if (end == null || !(end.at() instanceof souther.compiler.numeric.Count at)) {
            return null;
        }
        return new souther.compiler.numeric.RationalCut(
                souther.compiler.numeric.Rational.of(at.at()), end.inclusive());
    }

    /** What every rule reaching one position leaves its numbers, or null where the reading has no
     *  position for the term. */
    private static souther.compiler.numeric.NumericDomain.Bounds boundsOf(NumericTerm term,
                                                                          InputReads reads) {
        for (souther.compiler.inputs.Position position : reads.read().positions()) {
            if (position.term().equals(term)) {
                return position.numericDomain() != null ? position.numericDomain()
                        : term.ownBounds();
            }
        }
        return null;
    }

    /** What the operator of a line at a position states, which the reading of it already answered
     *  and holds as the three booleans a threshold is recorded with. */
    private static ComparisonClaim claimOf(ComparedLine drawn) {
        return drawn.singles() ? new ComparisonClaim.Singled(drawn.holdsAtTheValue())
                : new ComparisonClaim.Cut(drawn.valueBelongsBelow(), drawn.holdsAtTheValue());
    }

    /**
     * What this cuts, as the direction it runs.
     *
     * <p>Asked of the quantity rather than of which variant of quantity it is. A rule written
     * {@code 2 * n > 40} arrives as a form over twice a position and cuts the position, and a
     * reading that told those apart by the shape it was holding reported the model as drawing one
     * line through {@code n} where it draws two.
     */
    QuantityKey quantity() {
        return QuantityKey.of(direction(of));
    }

    /** How much of the quantity this rule wrote, which is what a level of one reads as on the
     *  other. */
    java.math.BigDecimal per() {
        return QuantityKey.per(direction(of));
    }

    /**
     * Where it parts that quantity's values, in the quantity's own units.
     *
     * <p>Found on the order the rule was written on, which is the order that knows which levels the
     * written form attains — {@code 2 * n <= 9} cuts the even numbers and nine is not one of them,
     * so the two sides part between eight and ten. Read back afterwards, which is exact: a level the
     * written form attains is a multiple of how much of the quantity it wrote.
     */
    Seam seam() {
        LinearForm<NumericTerm> direction = direction(of);
        java.math.BigDecimal per = QuantityKey.per(direction);
        return Seam.of(of.levels(), at,
                valueBelongsBelow() ? Towards.BELOW : Towards.ABOVE,
                new Seam.Scale(per, direction.coefs().size() == 1 ? of.carrier() : null));
    }

    /**
     * The form a quantity runs along, whichever of the three it is.
     *
     * <p>One position's own values are that position with a coefficient of one; how far two
     * positions stand apart is their difference; and a form is itself. The three used to be told
     * apart by every reader that wanted to know what a rule divided, and only one of them was
     * treated as dividing anything.
     */
    private static LinearForm<NumericTerm> direction(BorderQuantity of) {
        return switch (of) {
            case BorderQuantity.OfACoordinate one -> LinearForm.atom(one.term());
            case BorderQuantity.Apart two ->
                    LinearForm.<NumericTerm>atom(two.on()).minus(LinearForm.atom(two.against()));
            case BorderQuantity.OverAForm many -> many.form();
        };
    }

    /**
     * The position this cuts, where what it cuts is one position's own values. Null for every other
     * quantity, which is what tells a caller whether an axis is divided by this rule.
     *
     * <p><b>Asked of the canonical quantity and not of the shape the comparison arrived as.</b>
     * {@code 2 * n > 40} reaches this as a form over twice a position and divides that position at
     * twenty; read off the shape, it divided nothing, and a report counted two equivalence
     * partitions where the model states three.
     *
     * <p>Whether the line falls on a value of the position is a different question and not this
     * one. {@code 3 * d <= 1} cuts at a third, which no decimal this language writes, and the
     * behavior still answers one way below it and another way above — so the position has two
     * classes and no number to name the line by. Asked here, that answer made an equivalence
     * partition a thing this compiler can write a boundary for rather than a thing the model
     * distinguishes (issue #880).
     */
    NumericTerm dividedPosition() {
        java.util.Map<NumericTerm, java.math.BigDecimal> direction = quantity().direction();
        return direction.size() == 1 ? direction.keySet().iterator().next() : null;
    }

    /**
     * The one value of the position this rule names, or null where the position has none there.
     *
     * <p>Apart from {@link #dividedValue}, and the two are different questions that one answer had
     * been serving. A rule that orders the values around its line owes a row at the value beside the
     * line — {@code 2 * n <= 9} cuts between four and five and the row is written at four. A rule
     * that names a value names the line itself, and {@code 2 * n == 9} names no whole number at all
     * because nine halved is not one. Answered as the value beside the line, such a rule would put
     * four in a class of its own and four does not satisfy it.
     *
     * <p>Which is a fact about the position and not about the rule: that the canonical quantity is
     * one coordinate says the rule cuts that position, and whether the position has a value where
     * the line falls is asked of the order it sits on.
     */
    Place singledValue() {
        return seam().at().asAValueOf(of.carrier());
    }

    /**
     * The value of that position the classes either side of this line meet at.
     *
     * <p>Read off the seam rather than off the threshold, so a rule that wrote a multiple of the
     * position names a value the position holds: {@code 2 * n <= 9} parts the whole numbers between
     * four and five, and nine halved is not a whole number at all. Which of the two the classes meet
     * at is which side the threshold's own value belongs to, and that is the rule's to say.
     */
    Place dividedValue() {
        Seam seam = seam();
        Level side = valueBelongsBelow() ? seam.below() : seam.above();
        return side instanceof Level.OnACarrier on ? on.at() : null;
    }

    /** Whether the rule singles a value out rather than ordering the values around it. */
    boolean singles() {
        return claim instanceof ComparisonClaim.Singled;
    }

    /** Which side of the line the threshold's own value belongs to, which an equality does not
     *  answer — it orders nothing, so the side is written down as one answer and read by nobody. */
    boolean valueBelongsBelow() {
        return !(claim instanceof ComparisonClaim.Cut cut) || cut.valueBelongsBelow();
    }

    boolean holdsAtTheValue() {
        return switch (claim) {
            case ComparisonClaim.Cut cut -> cut.holdsAtTheValue();
            case ComparisonClaim.Singled singled -> singled.holdsAtTheValue();
            case ComparisonClaim.Nothing _ -> false;
        };
    }

    /** The line this draws, as a border reads it. */
    BoundaryTarget target() {
        return BoundaryTarget.at(of, at);
    }
}
