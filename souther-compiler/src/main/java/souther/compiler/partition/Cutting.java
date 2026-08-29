package souther.compiler.partition;

import souther.compiler.check.ComparisonClaim;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.NumericDomain.LinearForm;
import souther.compiler.numeric.Towards;

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
 * <p><b>The arithmetic first, and how it was written only where the arithmetic stopped.</b> The
 * canonical form says which quantity the rule cuts; what is left to decide is whether this compiler
 * can realize a line on the order that quantity is on. A reading of the operands is reached only
 * where the arithmetic had no answer at all — a date against a written date, a case of an
 * enumeration — so a spelling never settles a question the form has already settled. Tried first,
 * it did: {@code a <= a} came back a distance between two positions while the form had already
 * cancelled them, and the tautology was owed a row where the two hold one count.
 *
 * <p>Which levels the order has a place at is the order's own answer ({@link LevelSpace#canCutAt}).
 * Asked of the carrier instead — "do these values count" — two strings, which stand no measurable
 * distance apart and are still one above the other, were left with no line at the place they meet.
 *
 * @param of     what the rule cuts
 * @param at     where on it
 * @param claim  what the operator states about the threshold's own value
 * @param within what the rules leave the quantity itself. Three times a length is never negative,
 *               and a threshold outside where a quantity runs is one the rule draws no border at.
 *               Asked of every quantity alike, since what a quantity runs between is a question
 *               about the quantity
 */
record Cutting(BorderQuantity of, Level at, ComparisonClaim claim,
               souther.compiler.numeric.NumericDomain.Bounds within) {

    /**
     * What reading {@code comparison} as a line came to.
     *
     * <p>Three answers, and the two that are not a line are not one absence. A comparison whose
     * positions cancel was read from end to end and there was no line in it; one this compiler could
     * not take apart leaves whatever it states unknown. Told apart by a {@code null}, whoever asked
     * had to work out which — and worked it out by reading the comparison a second time, which is
     * how a rule read in full came to be described as one whose spelling defeated this compiler.
     */
    sealed interface Read {

        /** The line it draws. */
        record Cuts(Cutting cutting) implements Read {

            public Cuts {
                java.util.Objects.requireNonNull(cutting, "a comparison that cuts has a line");
            }
        }

        /** Read to the end, and the quantity it cuts is nothing. {@code read} is what the reading
         *  named on the way, which is what the rule is about however much of it cancelled
         *  ({@link AffineReading.OfAComparison.CutsNothing}). */
        record CutsNothing(java.util.Set<souther.compiler.inputs.NumericTerm> read)
                implements Read {

            public CutsNothing {
                read = java.util.Set.copyOf(read);
            }
        }

        /** The reading stopped, and this is what it stopped on. */
        record Stopped(souther.compiler.inputs.BlockReason.RuleReadingStopped why) implements Read {

            public Stopped {
                java.util.Objects.requireNonNull(why, "a reading that stopped says why");
            }
        }
    }

    /**
     * The same, said as which of the three it is.
     *
     * <p>The reason a reading stopped is settled here, where it stopped, and not asked for
     * afterwards by whoever met the absence. Worked out later, the reason came from a second walk
     * over the comparison and answered about the shape rather than about what this reading could do
     * with it.
     */
    static Read read(String behavior, Core.Binary comparison, InputReads reads, Symbols symbols,
                     souther.compiler.inputs.Quantities quantities) {
        AffineReading.OfAComparison canonical = AffineReading.read(comparison, reads, symbols);
        return switch (canonical) {
            // Nothing was missing: the form was read from end to end, and the quantity in it is
            // empty. Unconditional, and before anything about how the comparison was spelled —
            // `a <= a` names one position on either side and the arithmetic has already said the
            // two are one, so a reading of the operands finding a distance there is that reading
            // being wrong about the rule.
            case AffineReading.OfAComparison.CutsNothing over ->
                    new Read.CutsNothing(over.read());
            // The quantity is what the arithmetic says it is, and the realization is the only thing
            // left to try. Read the other way round, a spelling that produced a line took the
            // comparison before the canonical form was consulted at all.
            case AffineReading.OfAComparison.Cuts cuts ->
                    realized(behavior, cuts.read(), reads, symbols, quantities);
            // And only here does how it was written decide anything. The arithmetic stopped, which
            // is what a date against a written date and a case of an enumeration do: the values are
            // ones it cannot count, and the comparison still states a line.
            case AffineReading.OfAComparison.Stopped _ ->
                    asWritten(behavior, comparison, canonical, reads, symbols, quantities);
        };
    }

    /**
     * The same line, on the quantity taken at another position — or null where the quantity cannot
     * be taken there.
     *
     * <p>For a name that stands at more than one position. The comparison is read once and stays one
     * comparison; what moves is where its quantity is taken, and it is taken under each case a value
     * of the sum can turn out to be.
     *
     * <p>What the quantity runs between is worked out again here and not carried over. It is what
     * the rules leave the quantity, so a quantity taken somewhere else runs between whatever the
     * rules leave it there — kept as it was, a line would be held inside the values of the position
     * it came from.
     */
    Cutting movedTo(NumericTerm from, NumericTerm to, souther.compiler.inputs.TermOrders orders,
                    souther.compiler.inputs.Quantities quantities) {
        BorderQuantity moved = of.movedTo(from, to, orders);
        if (moved == null || !moved.levels().canCutAt(at)) {
            return null;
        }
        return new Cutting(moved, at, claim, quantities.runsBetween(direction(moved)));
    }

    /**
     * The line the canonical quantity draws, or the reading stopping on the order it is on.
     *
     * <p>Three shapes and one order among them, which is the arithmetic's: one position's own
     * values, two positions held apart, and a form over several. Nothing here reads the comparison
     * again — what each of them is handed is the form the reading already came to.
     */
    private static Read realized(String behavior, AffineReading read, InputReads reads,
                                 Symbols symbols,
                                 souther.compiler.inputs.Quantities quantities) {
        Cutting drawn = atAPosition(behavior, ComparedLine.fromTheForm(read, reads, symbols),
                quantities);
        if (drawn == null) {
            drawn = apart(behavior, ComparedTerms.fromTheForm(read, reads, symbols), read.claim(),
                    quantities);
        }
        if (drawn != null) {
            return new Read.Cuts(drawn);
        }
        Cutting form = overAForm(behavior, read, reads, symbols, quantities);
        if (form != null) {
            return new Read.Cuts(form);
        }
        // The quantity was read and no line could be built on it: a position with no order to be
        // counted on, or an order whose values this draws no line against. Its own answer and not
        // the form's — the form is right here, and it is the carrier that stopped this.
        return new Read.Stopped(new souther.compiler.inputs.BlockReason.UnreadComparisonDomain());
    }

    /**
     * The line the comparison draws as it was written, where the arithmetic could not read it.
     *
     * <p>The two readings that reach carriers the arithmetic cannot: a date against a written date,
     * a case of an enumeration, one string against another. Reached only from a reading that
     * stopped, so a spelling never answers a question the canonical form has already answered.
     */
    private static Read asWritten(String behavior, Core.Binary comparison,
                                  AffineReading.OfAComparison canonical, InputReads reads,
                                  Symbols symbols,
                                  souther.compiler.inputs.Quantities quantities) {
        Cutting drawn = atAPosition(behavior, ComparedLine.asWritten(comparison, reads, symbols),
                quantities);
        if (drawn == null) {
            drawn = apart(behavior, ComparedTerms.asWritten(comparison, reads, symbols),
                    ComparisonClaim.of(comparison.op()), quantities);
        }
        if (drawn != null) {
            return new Read.Cuts(drawn);
        }
        return new Read.Stopped(
                GuardThresholds.whyItStopped(comparison, canonical, reads, symbols));
    }

    /** One position's own values, cut where the reading found the line, or null where that reading
     *  found none and where the order has no place for the one it found. */
    private static Cutting atAPosition(String behavior, ComparedLine drawn,
                                       souther.compiler.inputs.Quantities quantities) {
        if (drawn == null) {
            return null;
        }
        return made(new BorderQuantity.OfACoordinate(AxisId.of(behavior, drawn.term()),
                        drawn.term(), drawn.orders()),
                new Level.OnACarrier(drawn.orders().answered(), drawn.value()), claimOf(drawn),
                quantities);
    }

    /** How far two positions stand apart, cut where the reading found the line, or null on the same
     *  two counts. */
    private static Cutting apart(String behavior, ComparedTerms drawn, ComparisonClaim claim,
                                 souther.compiler.inputs.Quantities quantities) {
        if (drawn == null) {
            return null;
        }
        return made(new BorderQuantity.Apart(behavior, drawn.on(), drawn.against(),
                        drawn.carriers()),
                new Level.ACount(drawn.stepsApart()), claim, quantities);
    }

    /**
     * One line, with what the rules leave the quantity it is on.
     *
     * <p>Asked of every quantity and not of the one shape that used to ask. What a quantity runs
     * between is a question about the quantity, which {@link #direction} answers for all three
     * alike; asked only where the quantity was a form, a rule cutting a length at a negative drew a
     * border where a length never goes, and a row was owed at a value no row can carry.
     *
     * <p>Asked of the reading of the input rather than composed from what each of the form's
     * positions runs between: a product of per-position answers cannot carry a rule relating them,
     * so two fields a record holds at five together came to ten and a border was drawn where the
     * model has nothing.
     */
    private static Cutting made(BorderQuantity of, Level at, ComparisonClaim claim,
                                souther.compiler.inputs.Quantities quantities) {
        // Whether the order has a place at that level for a line to be, which is the order's answer
        // and not the carrier's. An order whose only number is where two positions meet has one
        // place and no others; every order that counts is parted anywhere, whether or not it takes
        // the level itself.
        if (!of.levels().canCutAt(at)) {
            return null;
        }
        return new Cutting(of, at, claim, quantities.runsBetween(direction(of)));
    }

    /**
     * The line an arithmetic form over several positions draws.
     *
     * <p>Read where neither of the narrower readings could be, and about the same comparison. This
     * is the case domain testing exists for — a partition defined by a condition over more than one
     * variable — and the four sides of the box its positions sit in are not it.
     *
     * <p>Each position on the order it is written back on, which the reading answers per position.
     * Only where every one of them has an order with counts under it: a position with no number is
     * one a sum has nothing to add.
     *
     * <p><b>Whatever the operator states, and not orders alone.</b> {@code 2 * a == 8} names four
     * and {@code a + b == 10} names the place their sum reaches ten, and both are quantities this
     * reads. Refused here for not ordering its values, an equality over a form was reported as a
     * rule written in a form this compiler cannot take apart — a sentence about this compiler, and
     * the form is right here.
     */
    private static Cutting overAForm(String behavior, AffineReading read, InputReads reads,
                                     Symbols symbols,
                                     souther.compiler.inputs.Quantities quantities) {
        if (read == null || read.claim() instanceof ComparisonClaim.Nothing) {
            return null;
        }
        java.util.Map<NumericTerm, souther.compiler.inputs.TermOrders> on =
                read.carriers(reads, symbols);
        if (on == null) {
            return null;
        }
        return made(new BorderQuantity.OverAForm(behavior, read.form(), on),
                new Level.ACount(new Count(read.cut())), read.claim(), quantities);
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
                new Seam.Scale(per, direction.coefs().size() == 1
                        ? of.carrierOf(direction.coefs().keySet().iterator().next()) : null));
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
    NumericTerm.FromOnePosition dividedPosition() {
        java.util.Map<NumericTerm, java.math.BigDecimal> direction = quantity().direction();
        // And only where one position answers that number. A quantity read from somewhere else
        // divides no position however few terms it is over, so there is nothing here for a class
        // to be a class of.
        return direction.size() == 1
                ? direction.keySet().iterator().next().atOnePosition() : null;
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
        // On the order the position it divides is written on. A quantity used to answer with one
        // order for everything under it; a form may now be over positions written back differently,
        // and the value named here is a value of one of them.
        NumericTerm divides = dividedPosition();
        return seam().at().asAValueOf(divides == null ? null : of.carrierOf(divides));
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

    /**
     * Whether the quantity takes the level this rule names.
     *
     * <p>Asked of the quantity, which is what knows. {@code 2 * a == 8} names four and takes it;
     * {@code 2 * a == 9} takes the even numbers and nine is not one, so it names no value the
     * quantity holds; {@code a + b == 10} takes ten and {@code 2 * a + 2 * b == 9} does not. One
     * question, and the same answer whether the quantity is one position's own values or a form
     * over several.
     *
     * <p>Read off whether a value of a <em>position</em> could be written instead, this was the
     * wrong question wearing the right answer: a form over several positions has no value of a
     * position at all, so every rule singling one out on such a quantity came back naming nothing —
     * which is true of {@code 2 * a + 2 * b == 9} and false of {@code a + b == 10}.
     */
    boolean takesTheValueItNames() {
        return of.levels().attainable(at);
    }

    /**
     * The positions the canonical quantity is over, as a reader is sent to them.
     *
     * <p>What a rule that was read is filed at. The quantity is what the rule is about, so a
     * position the arithmetic cancelled is not one it says anything about: {@code a + b - b + c <=
     * 10} is {@code a + c <= 10}, and a note filed at {@code b} would say the rule relates a
     * position it does not mention.
     */
    java.util.List<souther.compiler.inputs.FilingCoordinate> over() {
        // By the position's own name, which is the one thing about a form that does not depend on
        // how it was written — the same order {@link AffineReading#ordered} puts a form's
        // coefficients in. Read off the map instead, the entries come back in an order salted once
        // per run, and a report is a document compared against the one written last time.
        return AffineReading.ordered(direction(of)).stream()
                .map(java.util.Map.Entry::getKey)
                .<souther.compiler.inputs.FilingCoordinate>map(
                        souther.compiler.inputs.FilingCoordinate::of)
                .distinct().toList();
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
