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

        /**
         * The arithmetic stopped, and this is what it leaves at each place it is filed at.
         *
         * <p>A map and not one reason, because the places are not one subject. Where the arithmetic
         * stopped, each place the walk met is a separate question — a position met inside an
         * expression this did not take apart says nothing about what that position carries — and
         * one answer handed to all of them told a position about the carrier of another.
         */
        record Stopped(java.util.SequencedMap<souther.compiler.inputs.FilingCoordinate,
                souther.compiler.inputs.BlockReason.RuleReadingStopped> why) implements Read {

            public Stopped {
                why = java.util.Collections.unmodifiableSequencedMap(
                        new java.util.LinkedHashMap<>(why));
            }
        }

        /**
         * The quantity was read and no line could be built on it: a position with no order to be
         * counted on, or an order whose values this draws no line against.
         *
         * <p>Its own answer and not {@link Stopped}. Nothing about the form fell short — it is
         * right here, and it is the carrier that stopped this — so the quantity is the subject and
         * the places are its own, which is what every read comparison's are. Said as a reading that
         * stopped, the places would come from a walk over the operands, and which of two authorities
         * a comparison's places came from would turn on which producer built the answer.
         *
         * @param over the coordinates of the quantity, which is where a reader is sent
         */
        record NoLineOnTheQuantity(
                java.util.List<souther.compiler.inputs.FilingCoordinate> over) implements Read {

            public NoLineOnTheQuantity {
                over = java.util.List.copyOf(over);
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
    static Read read(String behavior, Core.Binary comparison,
                     souther.compiler.inputs.InputDomain inputs, InputReads reads, Symbols symbols,
                     souther.compiler.inputs.Quantities quantities) {
        AffineReading.OfAComparison canonical =
                AffineReading.read(comparison, inputs, reads, symbols);
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
                    realized(behavior, cuts.read(), inputs, symbols, quantities);
            // And only here does how it was written decide anything. The arithmetic stopped, which
            // is what a date against a written date and a case of an enumeration do: the values are
            // ones it cannot count, and the comparison still states a line.
            case AffineReading.OfAComparison.Stopped stopped ->
                    asWritten(behavior, comparison, stopped, inputs, reads, symbols, quantities);
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
    private static Read realized(String behavior, AffineReading read,
                                 souther.compiler.inputs.InputDomain inputs, Symbols symbols,
                                 souther.compiler.inputs.Quantities quantities) {
        Cutting drawn = atAPosition(behavior, ComparedLine.fromTheForm(read, inputs, symbols),
                quantities);
        if (drawn == null) {
            drawn = apart(behavior, ComparedTerms.fromTheForm(read, inputs, symbols), read.claim(),
                    quantities);
        }
        if (drawn != null) {
            return new Read.Cuts(drawn);
        }
        Cutting form = overAForm(behavior, read, inputs, symbols, quantities);
        if (form != null) {
            return new Read.Cuts(form);
        }
        // The quantity was read and no line could be built on it. Filed at the quantity, because
        // the quantity is what the rule is about.
        return new Read.NoLineOnTheQuantity(
                AffineReading.filedAt(read.form().coefs().keySet()));
    }

    /**
     * The line the comparison draws as it was written, where the arithmetic could not read it.
     *
     * <p>The two readings that reach carriers the arithmetic cannot: a date against a written date,
     * a case of an enumeration, one string against another. Reached only from a reading that
     * stopped, so a spelling never answers a question the canonical form has already answered.
     */
    private static Read asWritten(String behavior, Core.Binary comparison,
                                  AffineReading.OfAComparison.Stopped canonical,
                                  souther.compiler.inputs.InputDomain inputs, InputReads reads,
                                  Symbols symbols,
                                  souther.compiler.inputs.Quantities quantities) {
        Cutting drawn = atAPosition(behavior,
                ComparedLine.asWritten(comparison, inputs, reads, symbols), quantities);
        if (drawn == null) {
            drawn = apart(behavior, ComparedTerms.asWritten(comparison, inputs, reads, symbols),
                    ComparisonClaim.of(comparison.op()), quantities);
        }
        if (drawn != null) {
            return new Read.Cuts(drawn);
        }
        return new Read.Stopped(
                GuardThresholds.whatEachPlaceIsLeftWith(comparison, canonical, inputs, reads,
                        symbols));
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
    private static Cutting overAForm(String behavior, AffineReading read,
                                     souther.compiler.inputs.InputDomain inputs, Symbols symbols,
                                     souther.compiler.inputs.Quantities quantities) {
        if (read == null || read.claim() instanceof ComparisonClaim.Nothing) {
            return null;
        }
        java.util.Map<NumericTerm, souther.compiler.inputs.TermOrders> on =
                read.carriers(inputs, symbols);
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
        // Where a reading that reached the numbers files them, which is one answer for every such
        // reading ({@link AffineReading#filedAt}): the terms themselves, in the order a document
        // names them. Written out here, a reader that reached the numbers by another way would
        // write it out again, and the two would file one rule at two coordinates.
        return AffineReading.filedAt(direction(of).coefs().keySet());
    }

    /**
     * What the rules leave this quantity, narrowed by what actually arrives at the comparison —
     * where the arrival is an interval of this quantity at all, and {@link #within} untouched where
     * it is not.
     *
     * <p>Whether it is lives here, because it is a reading of the quantity and the quantity is this
     * record's one answer. Asked by the caller instead, a second reader of the direction would stand
     * beside this one, free to disagree with it about what the rule is about.
     *
     * <p><b>The quantity is the position's own value, and nothing else is taken.</b> An arrival
     * states an interval of the value at one path, so it is an interval of this quantity exactly
     * where the two are the same value — a quantity that is some multiple of the position is on
     * another order, and its line is a level of that one. Taken with a change of units, the
     * arithmetic would be written for a shape no reader produces: what publishes an arrival is one
     * side of the comparison being that position, and the quantity such a comparison cuts is the
     * position itself. So the narrower rule is the whole of what is reachable, and what a multiple
     * costs is precision on a line that stands rather than an answer that is wrong.
     *
     * <p>Total over what it takes. An arrival this cannot project restricts nothing — not being
     * able to read a fact is not a proof — so the answer is what the declarations leave, unchanged.
     * The whole-state proof that nothing arrives is not taken here at all: that arm of the arrival
     * is no interval of anything, and a caller holds it apart ({@code ComparisonAssessment}).
     *
     * <p>Sound as a meet of two over-approximations: every arriving row is inside both, so a line
     * outside the meet is a line no arriving row reaches.
     */
    souther.compiler.numeric.NumericDomain.Bounds withinGiven(
            souther.compiler.reach.ComparisonArrival.Values arriving) {
        LinearForm<NumericTerm> direction = direction(of);
        if (direction.coefs().size() != 1 || direction.constant().signum() != 0) {
            return within;
        }
        java.util.Map.Entry<NumericTerm, java.math.BigDecimal> only =
                direction.coefs().entrySet().iterator().next();
        if (only.getValue().compareTo(java.math.BigDecimal.ONE) != 0
                || !(only.getKey() instanceof NumericTerm.ValueOf(var position))
                // The one thing this cannot read off its own quantity: which position the interval
                // is of. Both are the position the comparison turns on today and the check is what
                // says so — the day the two readings part, a line would be held inside the values of
                // somewhere else.
                || !position.equals(arriving.path())) {
            return within;
        }
        return within == null ? arriving.bounds() : within.meet(arriving.bounds());
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
