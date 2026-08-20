package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.check.ComparisonClaim;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.numeric.Count;

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
        java.math.BigDecimal least = java.math.BigDecimal.ZERO;
        java.math.BigDecimal most = java.math.BigDecimal.ZERO;
        for (java.util.Map.Entry<NumericTerm, java.math.BigDecimal> each
                : read.form().coefs().entrySet()) {
            souther.compiler.numeric.NumericDomain.Bounds bounds = boundsOf(each.getKey(), reads);
            Count low = bounds == null || bounds.min() == null
                    || !(bounds.min().at() instanceof Count at) ? null : at;
            Count high = bounds == null || bounds.max() == null
                    || !(bounds.max().at() instanceof Count at) ? null : at;
            if (low == null || high == null) {
                return null;
            }
            java.math.BigDecimal one = each.getValue().multiply(low.at());
            java.math.BigDecimal other = each.getValue().multiply(high.at());
            least = least.add(one.min(other));
            most = most.add(one.max(other));
        }
        return new souther.compiler.numeric.NumericDomain.Bounds(
                souther.compiler.numeric.Endpoint.inclusive(new Count(least)),
                souther.compiler.numeric.Endpoint.inclusive(new Count(most)));
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

    /** The position this cuts, where what it cuts is one position's own values. Null for every other
     *  quantity, which is what tells a caller whether an axis is divided by this rule. */
    NumericTerm dividedPosition() {
        return of instanceof BorderQuantity.OfACoordinate one ? one.term() : null;
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
