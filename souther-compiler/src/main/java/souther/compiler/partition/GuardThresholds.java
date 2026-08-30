package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.check.RuleAt;
import souther.compiler.check.RuleRef;
import souther.compiler.check.UnreadComparison;
import souther.compiler.check.ValueOrigin;
import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputNumber;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.ReadMeaning;
import souther.compiler.inputs.TermPath;
import souther.compiler.inputs.FilingCoordinate;
import souther.compiler.inputs.RuleWithoutALine;
import souther.compiler.numeric.Place;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.coverage.ComparisonCatalog;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.List;

/**
 * The values a behavior's body compares its inputs against.
 *
 * <p>A model's own thresholds, read where they are written. "Pre-approval is needed at a hundred
 * thousand" is not in any type — it is the comparison the behavior makes — and it is the line the
 * rows have to be written on both sides of.
 *
 * <p><b>A comparison is read wherever in a condition it is written</b> (spec
 * §boundary-coordinates). Which position the model divides is not a question about the
 * shape of the condition around the comparison, and it was answered as though it were: in
 *
 * <pre>if kind == Domestic &amp;&amp; cost &lt;= 100000</pre>
 *
 * the line at a hundred thousand went unread, and the position came back as one the model divides
 * no way — two tokens from the comparison that divides it.
 *
 * <p>Whether a comparison ran is not something the arms answer. A condition stops as soon as it is
 * settled, so under {@code A && B} an overseas request takes the else arm without {@code cost} having
 * been compared — and so does a request whose cost was compared and found too high. Each comparison
 * carries the site its own value is recorded at, which is what a line is measured against, and the
 * arms of the fork standing round it are read for nothing.
 *
 * <p>Three readers are kept apart and are easy to run together. Which comparisons exist is
 * {@link souther.compiler.coverage.ComparisonCatalog}'s answer and which of them a line may be drawn
 * on is {@link BoundaryPolicy}'s; which positions a comparison names at all is
 * {@link #mentioned}; which number a line can be drawn on is {@link InputNumber}'s. The last is the
 * narrowest, and asking it the first two questions is how a position a body compares became a
 * position nothing compares.
 */
public final class GuardThresholds {

    /**
     * What one reading of a body says about the comparisons in it.
     *
     * <p>One walk, because the operator is known once. Which side of the line the value itself is on
     * is not recoverable from a {@link Threshold} — {@code x <= c} and {@code x > c} both put
     * {@code c} on the low side and are two different rules about it — so it is read where the
     * operator is still in hand, and which values arrive is asked of the reading of the whole body.
     */
    public record Guards(List<LineEvidence> evidence,
                         List<RuleWithoutALine> rulesWithoutALine,
                         List<LineDrawn> between,
                         ReachingCuts reaching) {

        public static final Guards NONE =
                new Guards(List.of(), List.of(), List.of(), ReachingCuts.NONE);

        public Guards {
            evidence = List.copyOf(evidence);
            rulesWithoutALine = List.copyOf(rulesWithoutALine);
            between = List.copyOf(between);
        }

        /** The lines, read off what the walk said. Not a list of their own: the walk met these and
         *  the values it singled out in one order, and holding two lists loses it. */
        public List<Threshold> thresholds() {
            return LineEvidence.linesIn(evidence);
        }

        /** The values singled out, likewise. */
        public List<Singled> singled() {
            return LineEvidence.pointsIn(evidence);
        }

        /**
         * A value a body singles out rather than orders.
         *
         * <p>Apart from a {@link Threshold}, which says where one range ends and the next begins. An
         * equality says nothing about ranges: what it distinguishes is the value from every other
         * value, and reading it as a place to cut would put a distinction between the two sides into
         * a partition the model never drew.
         *
         * <p>A value a rule names, and the position it names it at.
         *
         * <p>A value and never an absence. What such a rule does is put one value in a class of its
         * own, so a rule that names none of the position's values singles nothing out and is not one
         * of these — asked for the value beside the line instead, a rule that names no whole number
         * would have put the number beside it in a class it does not satisfy.
         */
        public record Singled(NumericTerm.FromOnePosition term, Place value, OriginRef origin) {
            public Singled {
                if (value == null) {
                    throw new IllegalArgumentException(
                            "a rule that singles nothing out is not a value singled out: " + term);
                }
            }
        }

    }


    /**
     * The same, reading the input's rules here.
     *
     * <p>For a caller that has no reading of them in hand — nor of what arrives at each comparison,
     * which reads as restricting nothing, so every line such a caller reads is kept as the
     * declarations alone leave it. The pipeline that measures a behavior reads both once and hands
     * the same ones to everything that asks, since each of these reading its own is every rule of
     * every parameter read again to arrive at the same answers.
     */
    public static Guards of(String behavior, Core body, CoverageSites.Plan plan,
                            InputDomain inputs, Symbols symbols) {
        return of(behavior, body, plan, inputs, inputs.quantities(symbols), symbols,
                souther.compiler.check.ElementBindings.NONE,
                souther.compiler.check.PathReachability.Answers.NONE);
    }

    /** The thresholds one behavior's body compares its parameters against. {@code plan} supplies
     * the site each comparison's own value is recorded at, so a boundary can later ask whether the
     * comparison ran — which is not something the arms of anything standing round it record.
     * {@code arrives} says what the paths leave arriving at each of those sites, which is what a
     * line is dropped by ({@link ComparisonAssessment.NothingArrivesAtItsLine}). */
    public static Guards of(String behavior, Core body, CoverageSites.Plan plan,
                            InputDomain inputs, souther.compiler.inputs.Quantities quantities,
                            Symbols symbols,
                            souther.compiler.check.ElementBindings elements,
                            souther.compiler.check.PathReachability.Answers arrives) {
        List<LineEvidence> found = new ArrayList<>();
        List<RuleWithoutALine> withoutALine = new ArrayList<>();
        List<LineDrawn> between = new ArrayList<>();
        // One reading of the body, and everything below is that reading asked something. Where a
        // comparison is written, what its names point at, what a row had satisfied to get there,
        // whether a line may be drawn on it and what it came to are five questions about one
        // position, and one walk answers them about one position.
        ComparisonReadings read = ComparisonReadings.of(behavior, body, plan, inputs,
                InputReads.ofParameters(inputs.parameterReads(), elements), symbols, quantities,
                arrives);
        for (ComparisonReadings.Reading each : read.all()) {
            switch (each.standing()) {
                case BoundaryPolicy.Standing.Admitted admitted ->
                        lineAt(behavior, each.comparison(), plan, symbols,
                                admitted.read(), found, between, withoutALine);
                // Not a rule with no line here: its outcome is about no row, whichever of the
                // reasons refused it ({@link NotABoundary}), so there is nothing for a report to
                // say of it.
                case BoundaryPolicy.Standing.Refused _ -> { }
            }
        }
        return new Guards(found, withoutALine, between, read.reaching(plan));
    }

    /**
     * The positions the values a comparison is over came from, for a comparison that names none.
     *
     * <p>Beside {@link #mentioned} and asking the other question. That one says which positions the
     * terms <em>are</em>; this says where they came from, which is only ever asked once the first
     * has come back with nothing.
     */
    static void cameFrom(Core.Binary comparison, InputReads reads, Symbols symbols,
                                 List<TermPath> out) {
        for (Core side : List.of(comparison.left(), comparison.right())) {
            TermPath at = reads.cameFrom(side, symbols);
            if (at != null && !out.contains(at)) {
                out.add(at);
            }
        }
    }

    /**
     * Every position an expression names, however it is written.
     *
     * <p>Weaker than {@link InputNumber#of} on purpose, and asked instead of it. That one answers
     * whether a line can be drawn — it wants a number the terms name — and this one answers whether
     * the model says anything about a position at all. Sharing a reader between the two turns an expression
     * the derivation does not model into a position nothing compares: {@code p.x + 1 < 10} named no
     * position, and came back as one the model divides no way two tokens from a comparison about it.
     *
     * <p>What an expression is made of here, and what stood at each position it named.
     *
     * <p>The type comes back with the walk because the walk is where it is known. Whether a line can
     * be drawn on a position is asked of what the comparison compares — a position declared as one
     * case of an enumeration is ordered by its sum and carries none of the sum's places — and looked
     * up afterwards from the reading of the inputs it was the declaration's answer instead, which is
     * a different question about the same name.
     */
    record Names(ValueOrigin<TermPath> origin, java.util.Map<TermPath, Type> met) {}

    /** What {@code e} is made of, for a caller that has no use for the types. */
    static ValueOrigin<TermPath> originOf(Core e, InputReads reads, Symbols symbols) {
        return namesIn(e, reads, symbols).origin();
    }

    /** The same, with what stood at each position the walk met. */
    static Names namesIn(Core e, InputReads reads, Symbols symbols) {
        java.util.Map<TermPath, Type> met = new java.util.LinkedHashMap<>();
        return new Names(ValueOrigin.of(e, reads,
                new ValueOrigin.Reading<TermPath, InputReads>() {

            /**
             * A name is what the reading of the input says it is, and there are four answers rather
             * than a position and nothing. Only the first of them is a position; a name given
             * arithmetic over positions is read through, and the two that name nothing are told
             * apart by where the difference is read rather than here.
             */
            @Override
            public TermPath positionOf(Core here, InputReads at) {
                TermPath found = pathOf(here, at);
                if (found != null) {
                    met.putIfAbsent(found, here.type());
                }
                return found;
            }

            private TermPath pathOf(Core here, InputReads at) {
                if (here instanceof Core.Read read) {
                    return at.meaningOf(read, symbols) instanceof ReadMeaning.Position position
                            ? position.path() : null;
                }
                // A call the language defines the meaning of stands for what it answers and not for
                // a location, however the reading spells the two apart.
                return here instanceof Core.PreservedCall ? null : at.pathOf(here, symbols);
            }

            @Override
            public TermPath madeFrom(Core here, InputReads at) {
                return at.cameFrom(here, symbols);
            }

            /**
             * In the environment the answer came with, which is the one the arithmetic reads it in
             * too. Taking the one this walk happens to hold would be this reader deciding for
             * itself where a name's value is read, beside a reader that was told.
             */
            @Override
            public souther.compiler.check.AffineForms.ReadThrough<InputReads> readThrough(
                    Core.Read read, InputReads at) {
                return NameAnswers.denoting(read, at, symbols);
            }

            @Override
            public InputReads inside(Core.LetIn li, InputReads at) {
                return at.and(li.binder(), li.value());
            }
        }), met);
    }

    /**
     * What stopped the arithmetic's reading of this comparison, told where it stopped.
     *
     * <p>{@link UnreadComparison}'s answer, which is where it is so that an invariant's clause of
     * the same shape gets the same one. What is this reader's own is how a position is looked up:
     * a body's read of a parameter is what names one here, and a coordinate of a value is what
     * names one over there.
     *
     * <p>Only for a reading that stopped, which the parameter says. A comparison the arithmetic
     * read to the end has its answer in what it read — a line, or a quantity that is nothing — and
     * none of that is a stop; handed the sides of such a comparison, this would describe a form
     * that was read as one that was not. Where the reading stopped, the expression and the
     * environment it was being read in come back together, so the sides are not read again in
     * whatever the caller happens to hold.
     */
    static java.util.SequencedMap<FilingCoordinate, BlockReason.RuleReadingStopped>
            whatEachPlaceIsLeftWith(Core.Binary comparison,
                                    AffineReading.OfAComparison.Stopped stopped,
                                    InputDomain inputs, InputReads reads, Symbols symbols) {
        Names left = namesIn(comparison.left(), reads, symbols);
        Names right = namesIn(comparison.right(), reads, symbols);
        Names here = namesIn(stopped.node(), stopped.at(), symbols);
        java.util.Map<TermPath, Type> met = new java.util.LinkedHashMap<>(left.met());
        right.met().forEach(met::putIfAbsent);
        here.met().forEach(met::putIfAbsent);
        UnreadComparison.Quantity.NotRead<TermPath> notRead =
                new UnreadComparison.Quantity.NotRead<>(here.origin());
        java.util.function.Predicate<TermPath> ordered =
                at -> met.containsKey(at) && orderable(met.get(at), symbols);
        java.util.SequencedMap<FilingCoordinate, BlockReason.RuleReadingStopped> out =
                new java.util.LinkedHashMap<>();
        for (FilingCoordinate at : filedAt(comparison, inputs, reads, symbols)) {
            out.putIfAbsent(at,
                    UnreadComparison.whereItStopped(ruleAt(at, left, right), notRead, ordered));
        }
        return out;
    }

    /**
     * What a rule filed at {@code at} is about, as this reader knows it.
     *
     * <p>The values at a position where a whole side of the comparison is that position and nothing
     * else. {@code s < Won} states something about the values of {@code s}, whatever the reading
     * made of the other side; {@code n < l1.l2.leaf.x} states nothing about the values of
     * {@code l1.l2.leaf}, which is where the walk happened to meet a position on its way through an
     * expression it could not take apart.
     *
     * <p>And of the position's own value, not of a number taken of it. A rule about a length is
     * filed at the length, and what strings are ordered on is no part of what it says.
     *
     * <p>Which is the same question the reading of clauses answers of its own coordinates, put in
     * this reader's names. Answered from the coordinate alone, {@code s < Won} came out as a rule
     * about something other than {@code s}: the coordinate says the reading named no number there,
     * and there is no number to name — the values of a case of a sum are not counted.
     */
    private static RuleAt<TermPath> ruleAt(FilingCoordinate at, Names left, Names right) {
        TermPath here = at instanceof FilingCoordinate.OfTerm it
                && !(it.term() instanceof NumericTerm.ValueOf) ? null : at.path();
        return here != null && (isExactly(left.origin(), here) || isExactly(right.origin(), here))
                ? new RuleAt.AboutOwnValues<>(at.path())
                : new RuleAt.NotAboutOwnValues<>(at.path());
    }

    /** Whether a whole side of the comparison is the position at {@code path} and nothing else. */
    private static boolean isExactly(ValueOrigin<TermPath> side, TermPath path) {
        return side instanceof ValueOrigin.IsAPosition<TermPath> one && one.at().equals(path);
    }

    /**
     * What one side of a comparison came to here.
     *
     * <p>Which positions it names is {@link #mentioned}'s recursive question and which number a
     * line could be drawn on is {@link InputNumber}'s narrower one, and the two are what tell a
     * position inside an expression from a position. Asked the narrow question alone,
     * {@code y + 1} named nothing and a comparison of two positions came back as a form nobody
     * could read.
     *
     * <p>The positions come from the one walk either way. Read again off the term where there is
     * one, a side would be carrying two answers to "which position is this about" and the
     * comparison between them would be settled by whichever the caller looked at.
     */
    static List<TermPath> mentionedIn(Core e, InputReads reads, Symbols symbols) {
        return new ArrayList<>(originOf(e, reads, symbols).positions());
    }

    /**
     * Which numbers of the input a comparison was read for, for a reader that stopped on it.
     *
     * <p>Where the reading was looking, and never what the rule is about. A comparison this could
     * not read leaves what it states unknown — {@code a * a + b - b <= 9} is filed at both
     * positions, and the arithmetic that would have cancelled {@code b} is the part that stopped —
     * so nothing here may become the subject of a question.
     *
     * <p>The number where a side names one, and the position where none was named. A rule about a
     * length that nothing could read leaves the length short and the string alone, so a side the
     * term reading names is filed as the term it is. A position the walk met inside something it
     * could not take apart is filed as the position, and that is not a claim that the rule is about
     * the position's own values — which number of it the rule is about is exactly the part that was
     * not read.
     */
    static List<FilingCoordinate> filedAt(Core.Binary comparison, InputDomain inputs,
                                               InputReads reads, Symbols symbols) {
        List<FilingCoordinate> out = new ArrayList<>();
        for (Core side : List.of(comparison.left(), comparison.right())) {
            Named named = namedBy(side, inputs, reads, symbols);
            if (named != null) {
                // The term itself, because this side named one: a rule about a length that nothing
                // could read leaves the length short and the string's own values alone.
                add(FilingCoordinate.of(named.term()), out);
            }
        }
        for (TermPath each : mentionedIn(comparison, reads, symbols)) {
            if (out.stream().noneMatch(had -> had.path().equals(each))) {
                add(FilingCoordinate.at(each), out);
            }
        }
        return out;
    }

    private static void add(FilingCoordinate here, List<FilingCoordinate> out) {
        if (!out.contains(here)) {
            out.add(here);
        }
    }

    /** The same, added to what a caller has already gathered from beside it. */
    private static void mentioned(Core e, InputReads reads, Symbols symbols, List<TermPath> out) {
        for (TermPath each : originOf(e, reads, symbols).positions()) {
            if (!out.contains(each)) {
                out.add(each);
            }
        }
    }

    /**
     * The line one comparison draws, where anything of it can be read.
     *
     * <p>One comparison is one line however many positions it mentions, and what it cuts is
     * {@link Cutting}'s one answer. What is added here is what meeting it takes, which is this
     * rule's own and no other's.
     *
     * <p>Whether a line may be drawn on this comparison at all was settled before the walk got
     * here, by {@link BoundaryPolicy}, and what the comparison comes to was read where that was
     * settled ({@code read}). Nothing here reads the comparison again.
     */
    private static void lineAt(String behavior, Core.Binary each, CoverageSites.Plan plan,
                               Symbols symbols, ComparisonAssessment read,
                               List<LineEvidence> out,
                               List<LineDrawn> between,
                               List<RuleWithoutALine> withoutALine) {
        // The plan numbered every comparison of an instrumented condition before anything read a
        // line off one, so this is here. Required rather than looked up leniently: a line whose
        // comparison has no site is this reader and the plan disagreeing about what a condition
        // is made of.
        souther.compiler.coverage.ComparisonOccurrence site =
                plan.requireComparisonAt(each);
        publish(behavior, each, plan, read, withoutALine);
        switch (read) {
            case ComparisonAssessment.AtAPosition at -> {
                OriginRef.ComparisonOrigin origin = originOf(behavior, each, site, plan,
                        at.cutting());
                // The value a row is owed against this line, which the reading of the comparison
                // already answered. Taken off the level the rule was written with, a rule that wrote
                // a multiple of the position named a class at a number the position never holds.
                if (at.cutting().singles()) {
                    // The value the rule names, which is where its line falls and not the value
                    // beside it. A rule that names no value of the position singles nothing out
                    // here — the position is divided all the same, and what divides it is the line.
                    if (at.value() != null) {
                        out.add(new LineEvidence.Singles(
                                new Guards.Singled(at.position(), at.value(), origin)));
                    }
                } else {
                    out.add(new LineEvidence.Divides(new Threshold(at.position(),
                            at.cutting().seam(), at.cutting().valueBelongsBelow(), origin)));
                }
                // And the line itself, where the position has no value beside it for a row to be
                // owed at. It divides the position — the classes either side are what the model
                // tells apart — and the border is drawn on the quantity the rule wrote, which can
                // name where the line falls. Left out, a rule that cuts at a third had its classes
                // counted and nothing said about its line at all.
                if (at.value() == null && at.drawsABorder()) {
                    between.add(new LineDrawn(at.cutting(), origin));
                }
            }
            // A line on something that is not one position's own values. What the partition could
            // not read here it still could not read, and a boundary answering does not answer for
            // it (spec §example-partition).
            //
            // Collected rather than turned into a border here. What a border owes away from
            // its line is a run of the arrangement every rule about that quantity makes
            // together, and a border built where its comparison was read knows only its own
            // line — so a second rule over one form left the first one's run going to the end
            // of the order, past it.
            case ComparisonAssessment.AcrossPositions over -> {
                // A value singled out on such a quantity has no sides, so there is nothing for a
                // border to owe a row away from: `a == b` puts the whole of one arm on the place
                // the two meet, and that arm is a row the branch measure already asks for.
                if (over.drawsABorder()) {
                    between.add(new LineDrawn(over.cutting(),
                            originOf(behavior, each, site, plan, over.cutting())));
                }
            }
            case ComparisonAssessment.AnswerDependent _, ComparisonAssessment.NoInput _,
                 ComparisonAssessment.CutsNothing _, ComparisonAssessment.OutsideTheDomain _,
                 ComparisonAssessment.NothingArrivesAtItsLine _,
                 ComparisonAssessment.NoFeasibleInput _,
                 ComparisonAssessment.Unread _ -> { }
        }
    }

    /**
     * What the assessment leaves the positions the comparison names, said in its own words.
     *
     * <p>Two of the arms leave something. A line over a form divides no position, so each position
     * it names is left with no class of its own from this rule — nothing fell short, and the rule
     * says as much. A reading that stopped leaves whatever the rule states unknown, and its own
     * reason for stopping is what says which measures are thereby short of something.
     *
     * <p>The rest leave nothing. A line on a position divides it; and a comparison about no position
     * of the input, or about what the behavior answers, was never about a position for anything to
     * be left at.
     *
     * <p>Which of them it is, is {@link ComparisonAssessment#whatEachPlaceIsLeftWith}'s and not
     * this reader's. The same table stood here and in the clause reader, so a case added to an
     * assessment had to be answered twice; and worked out from the comparison afterwards rather
     * than where the reading stopped, one whose carrier stopped the reading came back as a rule
     * relating two positions — a sentence saying no measure is short of anything, over a model
     * missing a border.
     */
    private static void publish(String behavior, Core.Binary comparison, CoverageSites.Plan plan,
                                ComparisonAssessment read, List<RuleWithoutALine> out) {
        RuleRef.Comparison rule = new RuleRef.Comparison(behavior, comparison.origin());
        souther.compiler.check.RuleCitation cited = citationOf(comparison, plan.comparisons());
        // What each place is left with, and which places there are, are the assessment's one
        // answer. A rule that was read is filed at its quantity's coordinates and says one thing
        // there, because the quantity is one subject; a reading that stopped has none, and each
        // place says what stopped it there.
        read.whatEachPlaceIsLeftWith().forEach((at, why) -> {
            RuleWithoutALine said = new RuleWithoutALine(rule, cited, at, why);
            if (out.stream().noneMatch(had -> had.sameAs(said))) {
                out.add(said);
            }
        });
    }

    /** How a row meets a line a body's condition drew, which is a guard's own answer: what it takes
     *  is getting the comparison to answer, because what it is about is a place in a body. */
    private static OriginRef.ComparisonOrigin originOf(String behavior, Core.Binary each,
                                                       souther.compiler.coverage
                                                               .ComparisonOccurrence site,
                                                       CoverageSites.Plan plan, Cutting cutting) {
        return new OriginRef.ComparisonOrigin(
                new RuleRef.Comparison(behavior, each.origin()),
                new OriginRef.ComparisonOrigin.Read(site, citationOf(each, plan.comparisons())),
                cutting.valueBelongsBelow(), cutting.holdsAtTheValue(), cutting.singles());
    }

    /**
     * How a reader finds a comparison, which is where it is written.
     *
     * <p>Nothing from what stands around it. The construct came from the fork the comparison was
     * written into — the word a reader looks for — and that made the handle for a rule depend on
     * something the rule has no part of: a condition holding two comparisons is two rules under one
     * construct, and a comparison given a name a line above the fork is the same rule with no fork
     * over it at all.
     *
     * <p>Read off the catalog rather than taken from the node again. Where a comparison is written
     * is a fact about the comparison, and the catalog is what holds those — taken here as well, it
     * would be a second answer to a question already answered, which is what this whole reading is
     * about.
     */
    static souther.compiler.check.RuleCitation.WrittenAt citationOf(Core.Binary comparison,
                                                                    ComparisonCatalog catalog) {
        return new souther.compiler.check.RuleCitation.WrittenAt(
                catalog.at(comparison).orElseThrow(() -> new IllegalStateException(
                        "a rule was cited at a comparison this catalog does not hold, at "
                                + comparison.pos())).at());
    }

    /** Whether a line can be drawn on what this type carries, asked of the one place that says so. */
    static boolean orderable(Type type, Symbols symbols) {
        return Carrier.ofValue(type, symbols) != null;
    }

    /**
     * The number an expression names and the order that number is read and written on.
     *
     * @param term  what the expression names
     * @param order what it is counted on
     */
    record Named(NumericTerm term, souther.compiler.inputs.TermOrders orders) {

        /** What a line on it is measured on, which is what most readers of a pair want. */
        Carrier order() {
            return orders.answered();
        }
    }

    /**
     * The same, or null where the expression names no number this can put an order under.
     *
     * <p>The two together because no reader of a line wants one without the other, and both readings
     * of a comparison want them the same way round. Neither answer is made here: which position an
     * expression names is {@link InputNumber}'s and which order that position is counted on is the
     * reading of the declarations' ({@link InputDomain#carrierOf}).
     *
     * <p>In particular the expression's own type is not read, here or anywhere a line is drawn. It
     * would agree wherever a rule names its positions itself and disagree wherever an operation
     * stands between them: the operands of {@code Date.daysBetween(a, b) > 10} are whole numbers
     * where its positions hold dates. Taking the order off the comparison wrote both positions back
     * as whole numbers and read them off a row as whole numbers, which agreed with itself about a
     * border nothing could meet (#1018).
     */
    static Named namedBy(Core e, InputDomain inputs, InputReads reads, Symbols symbols) {
        NumericTerm term = InputNumber.of(e, inputs, reads, symbols);
        if (term == null) {
            return null;
        }
        souther.compiler.inputs.TermOrders orders = inputs.ordersOf(term, symbols);
        return orders.answered() == null ? null : new Named(term, orders);
    }

    private GuardThresholds() {}
}
