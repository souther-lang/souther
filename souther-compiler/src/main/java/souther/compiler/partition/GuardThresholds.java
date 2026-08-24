package souther.compiler.partition;

import souther.compiler.check.NumericMeasures;
import souther.compiler.check.Carrier;
import souther.compiler.check.Required;
import souther.compiler.check.RuleAccounting;
import souther.compiler.check.RuleRef;
import souther.compiler.check.UnreadComparison;
import souther.compiler.check.ValueOrigin;
import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.ReadMeaning;
import souther.compiler.inputs.TermPath;
import souther.compiler.inputs.UnreadRule;
import souther.compiler.numeric.Place;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.coverage.ComparisonCatalog;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.diag.Citation;
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
 * {@link #mentioned}; which number a line can be drawn on is {@link #termOf}. The last is the
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
    public record Guards(List<Threshold> thresholds,
                         List<UnreadRule> unread, List<Singled> singled,
                         List<LineDrawn> between,
                         List<AtAPosition> accounting,
                         ReachingCuts reaching) {

        public static final Guards NONE =
                new Guards(List.of(), List.of(), List.of(), List.of(), List.of(),
                        ReachingCuts.NONE);

        /**
         * One comparison's accounting, and the position a reader is sent to for it.
         *
         * <p>The position is beside the accounting rather than inside it. What a rule raises is
         * about a subject of its own — the number a line falls on — and where in a behavior's inputs
         * that number is read from is what a document keys the question by, which is a question
         * about the walk that found it.
         */
        public record AtAPosition(TermPath at, NumericTerm term, RuleAccounting accounting) {
            public AtAPosition {
                if (at == null || accounting == null) {
                    throw new IllegalArgumentException("an accounting is filed somewhere");
                }
            }
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
        public record Singled(NumericTerm term, Place value, OriginRef origin) {
            public Singled {
                if (value == null) {
                    throw new IllegalArgumentException(
                            "a rule that singles nothing out is not a value singled out: " + term);
                }
            }
        }

        public Guards {
            thresholds = List.copyOf(thresholds);
            unread = List.copyOf(unread);
            accounting = List.copyOf(accounting);
            singled = List.copyOf(singled);
            between = List.copyOf(between);
        }
    }


    /**
     * The same, reading the input's rules here.
     *
     * <p>For a caller that has no reading of them in hand. The pipeline that measures a behavior
     * reads them once and hands the same one to everything that asks, since each of these reading
     * its own is every rule of every parameter read again to arrive at the same answers.
     */
    public static Guards of(String behavior, Core body, CoverageSites.Plan plan,
                            InputDomain inputs, Symbols symbols) {
        return of(behavior, body, plan, inputs, inputs.quantities(symbols), symbols,
                souther.compiler.check.ElementBindings.NONE);
    }

    /** The thresholds one behavior's body compares its parameters against. {@code plan} supplies
     * the site each comparison's own value is recorded at, so a boundary can later ask whether the
     * comparison ran — which is not something the arms of anything standing round it record. */
    public static Guards of(String behavior, Core body, CoverageSites.Plan plan,
                            InputDomain inputs, souther.compiler.inputs.Quantities quantities,
                            Symbols symbols,
                            souther.compiler.check.ElementBindings elements) {
        List<Threshold> found = new ArrayList<>();
        List<UnreadRule> unread = new ArrayList<>();
        List<Guards.AtAPosition> accounting = new ArrayList<>();
        List<Guards.Singled> singled = new ArrayList<>();
        List<LineDrawn> between = new ArrayList<>();
        // The comparisons a line came of, and not the positions they were about. A position carries
        // more than one statement and reading one of them settles nothing about the others.
        List<Core> made = new ArrayList<>();
        // Every line the body draws, read where the comparison that draws it is written and under
        // the names in force there. Which comparisons those are is
        // {@link BoundaryPolicy}'s answer: a reader that had to find a fork before it could
        // find a rule could not be handed a wider one without being rewritten.
        // One reading of the body, and everything below is that reading asked something. Where a
        // comparison is written, what its names point at, what a row had satisfied to get there and
        // whether a line is drawn on it are four questions about one position, and a walk apiece was
        // a walk apiece to disagree about what a `let` does.
        ComparisonReadings read = ComparisonReadings.of(body, plan, InputReads.of(inputs, elements), symbols);
        for (ComparisonReadings.Reading each : read.drawn()) {
            lineAt(behavior, each.comparison(), plan, each.reads(), symbols, quantities, found,
                    singled, between, accounting, made);
        }
        // And every comparison the model states something by that nothing turned into a line.
        noticed(behavior, read, made, plan, symbols, unread);
        return new Guards(found, unread, singled, between, accounting, read.reaching(plan));
    }

    /**
     * Every comparison the model states something by that nothing turned into a line.
     *
     * <p>Asked of the comparisons and not of the positions. One position carries more than one
     * statement, and a line read at it says nothing about the rest: kept per position, a threshold
     * on `x` swallowed the comparison beside it that nothing could read, which is "a result exists,
     * so the reading is complete".
     *
     * <p>Read off the same answer the lines came off, and not from a walk of its own. Both used to
     * start from a fork, and a comparison written anywhere else came back neither a line nor a rule
     * this could not read — it came back unmentioned, which is the one answer that says the model
     * states nothing at the position. Two walks agreeing about which comparisons there are is
     * something to keep in step; one answer read twice is not.
     *
     * <p>A wider set than the one that bears lines, and deliberately. What this establishes is that
     * the model states something at a position — which is exactly what {@code not derivable} would
     * otherwise deny — so a comparison a line could never be drawn from is still a rule the author
     * wrote and still worth saying went unread.
     *
     * <p>Which is why a comparison nothing can measure is in and one nothing reads is out, and the
     * split is the same one {@link NotABoundary} is made of. {@link NotABoundary#NOTHING_RECORDS_IT}
     * and {@link NotABoundary#REPEATED_IN_ONE_RUN} are the author's rules, written at a position,
     * that this could not draw a line from — the sentence {@code not read} is there to say.
     * {@link NotABoundary#NOTHING_READS_IT} is not a rule of the model at all, and saying it went
     * unread would put a statement into the report that the behavior does not make.
     */
    private static void noticed(String behavior, ComparisonReadings read, List<Core> made,
                                CoverageSites.Plan plan, Symbols symbols, List<UnreadRule> out) {
        for (ComparisonReadings.Reading reading : read.all()) {
            if (reading.standing() instanceof BoundaryPolicy.Standing.DrawsNone none
                    && none.why() == NotABoundary.NOTHING_READS_IT) {
                continue;
            }
            Core.Binary binary = reading.comparison();
            // By the comparison it is, and not by what it was about: two comparisons at one position
            // are two statements, and this one having been read is no answer about the other.
            if (made.stream().anyMatch(each -> each == binary)) {
                continue;
            }
            ComparisonCatalog.Comparison entry = plan.comparisons().at(binary).orElse(null);
            if (entry == null || !writtenHere(entry)) {
                continue;
            }
            InputReads reads = reading.reads();
            List<TermPath> named = new ArrayList<>();
            mentioned(binary.left(), reads, symbols, named);
            mentioned(binary.right(), reads, symbols, named);
            final BlockReason.AboutARule why = why(binary, reads, symbols);
            // The rule the author wrote, read off the source. Which comparison it is is the
            // behavior and the construct the source wrote; where a reader is sent is where it is
            // written. Neither comes from the plan: a comparison in a fork both of whose arms can
            // record nothing is numbered nowhere, and a model states its rules regardless.
            RuleRef.Comparison rule = new RuleRef.Comparison(behavior, binary.origin());
            souther.compiler.check.RuleCitation cited = citationOf(binary, plan.comparisons());
            // A comparison naming no position of the input, whose terms came from one. Where the
            // rule is filed and nothing else: what it says is the reading's answer, and deciding it
            // here made the same fact about one comparison come out one way for an element and
            // another for a number — which is not a difference between the two rules.
            if (named.isEmpty()) {
                cameFrom(binary, reads, symbols, named);
            }
            for (TermPath each : named) {
                // One per position the comparison names, and told from its neighbours by the rule as
                // well as the place. Kept by position alone, the second comparison of one condition
                // about one position was dropped as a repeat of the first — which is the defect this
                // finding is about, one level in.
                UnreadRule said = new UnreadRule(rule, cited, each, why);
                if (out.stream().noneMatch(had -> had.sameAs(said))) {
                    out.add(said);
                }
            }
        }
    }

    /**
     * The positions the values a comparison is over came from, for a comparison that names none.
     *
     * <p>Beside {@link #mentioned} and asking the other question. That one says which positions the
     * terms <em>are</em>; this says where they came from, which is only ever asked once the first
     * has come back with nothing.
     */
    private static void cameFrom(Core.Binary comparison, InputReads reads, Symbols symbols,
                                 List<TermPath> out) {
        for (Core side : List.of(comparison.left(), comparison.right())) {
            TermPath at = reads.cameFrom(side, symbols);
            if (at != null && !out.contains(at)) {
                out.add(at);
            }
        }
    }

    /**
     * Whether this comparison is written in code this compile can send a reader to.
     *
     * <p>A call is spliced into the body that makes it, so a comparison written in something else
     * stands in this tree. Where that something else is out of sight — a library this compile has
     * no file for — the comparison is not a rule anybody reading this behavior can act on:
     * {@code Int.clamp(0, 100, n) > 70} is one comparison an author wrote and two they cannot open,
     * and naming the second two tells them to edit a function they do not have.
     *
     * <p>A helper of their own is not one of these. It has a file, the report cites it where it is
     * written, and it is theirs to rewrite — so the line is drawn at what a reader can reach and
     * not at whether an expansion happened.
     *
     * <p>{@link Citation} and not the position, which cannot say this: a spliced node carries the
     * coordinates of the code it was copied from. {@link Citation.Elsewhere} is exactly "written
     * where this compile has no file", and it is the same answer
     * {@link souther.compiler.check.RuleCitation} renders.
     *
     * <p>Read off the catalog, which holds where a comparison is written. Taken from the node again
     * here, this was one more place deciding for itself what the catalog already answers — and the
     * one deciding whether an author is told to edit a file they do not have.
     *
     * <p>Asked of the comparison and not of the fork above it. The one the author wrote sits
     * outside an expansion whose insides they did not, so a subtree is the wrong unit — and the
     * walk still goes through the expansion, because that is where a call's argument is bound and
     * a comparison read without it is about nothing.
     */
    private static boolean writtenHere(ComparisonCatalog.Comparison comparison) {
        return !(comparison.at() instanceof Citation.Elsewhere);
    }

    /**
     * Every position an expression names, however it is written.
     *
     * <p>Weaker than {@link #termOf} on purpose, and asked instead of it. That one answers whether a
     * line can be drawn — it wants a number the terms name — and this one answers whether the model
     * says anything about a position at all. Sharing a reader between the two turns an expression
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
                return at.meaningOf(read, symbols) instanceof ReadMeaning.Through through
                        ? new souther.compiler.check.AffineForms.ReadThrough<>(
                                through.value(), through.at())
                        : null;
            }

            @Override
            public InputReads inside(Core.LetIn li, InputReads at) {
                return at.and(li.binder(), li.value());
            }
        }), met);
    }

    /**
     * What would have to change before this comparison could be a line.
     *
     * <p>{@link UnreadComparison}'s, which is where the answer is so that an invariant's clause of
     * the same shape gets the same one. What is this reader's own is how a position is looked up:
     * a body's read of a parameter is what names one here, and a coordinate of a value is what
     * names one over there.
     */
    static BlockReason.AboutARule why(Core.Binary comparison, InputReads reads,
                           Symbols symbols) {
        Names left = namesIn(comparison.left(), reads, symbols);
        Names right = namesIn(comparison.right(), reads, symbols);
        java.util.Map<TermPath, Type> met = new java.util.LinkedHashMap<>(left.met());
        right.met().forEach(met::putIfAbsent);
        return UnreadComparison.why(left.origin(), right.origin(),
                quantityOf(comparison, reads, symbols, met),
                at -> met.containsKey(at) && orderable(met.get(at), symbols));
    }

    /**
     * The positions the quantity this comparison cuts is over, or null where the arithmetic read no
     * form at all.
     *
     * <p>This reader's own, because the atoms are: a body names a position by what it reads of a
     * parameter. What is done with the answer is {@link UnreadComparison}'s, so a clause of the same
     * shape two declarations away is described in the same words.
     */
    private static UnreadComparison.Quantity<TermPath> quantityOf(Core.Binary comparison,
                                                                  InputReads reads,
                                                                  Symbols symbols,
                                                                  java.util.Map<TermPath, Type> met) {
        // Each of the three the reading can come to, and no fourth made out of an absence. Where it
        // stopped, the expression and the environment it was being read in come back together, so
        // this does not read it again in whatever it happens to hold.
        switch (AffineReading.read(comparison, reads, symbols)) {
            case AffineReading.OfAComparison.Stopped stopped -> {
                Names here = namesIn(stopped.node(), stopped.at(), symbols);
                here.met().forEach(met::putIfAbsent);
                return new UnreadComparison.Quantity.NotRead<>(here.origin());
            }
            case AffineReading.OfAComparison.CutsNothing _ -> {
                return new UnreadComparison.Quantity.CutsNothing<>();
            }
            case AffineReading.OfAComparison.Cuts cuts -> {
                java.util.Set<TermPath> over = new java.util.LinkedHashSet<>();
                for (NumericTerm atom : cuts.read().form().coefs().keySet()) {
                    over.add(atom.path());
                }
                return new UnreadComparison.Quantity.Over<>(over);
            }
        }
    }

    /**
     * What one side of a comparison came to here.
     *
     * <p>Which positions it names is {@link #mentioned}'s recursive question and which number a
     * line could be drawn on is {@link #termOf}'s narrower one, and the two are what tell a
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
     * here, by {@link BoundaryPolicy}. Asked at the fork instead, this reader had to find one
     * to find a rule.
     */
    private static void lineAt(String behavior, Core.Binary each, CoverageSites.Plan plan,
                               InputReads reads, Symbols symbols,
                               souther.compiler.inputs.Quantities quantities,
                               List<Threshold> out, List<Guards.Singled> singled,
                               List<LineDrawn> between, List<Guards.AtAPosition> accounting,
                               List<Core> made) {
        // The plan numbered every comparison of an instrumented condition before anything read a
        // line off one, so this is here. Required rather than looked up leniently: a line whose
        // comparison has no site is this reader and the plan disagreeing about what a condition
        // is made of.
        souther.compiler.coverage.ComparisonOccurrence site =
                plan.requireComparisonAt(each);
        // What the comparison cuts is one question with one answer ({@link Cutting}). What is
        // added here is what meeting the line takes, which is a guard's own answer and no other
        // rule's.
        Cutting cutting = Cutting.of(behavior, each, reads, symbols, quantities);
        if (cutting == null) {
            raisesNoLine(accounting, behavior, plan.comparisons(), each, reads, symbols);
            return;
        }
        OriginRef.ComparisonOrigin origin = new OriginRef.ComparisonOrigin(
                new RuleRef.Comparison(behavior, each.origin()),
                new OriginRef.ComparisonOrigin.Read(site, citationOf(each, plan.comparisons())),
                cutting.valueBelongsBelow(), cutting.holdsAtTheValue(),
                cutting.singles());
        NumericTerm divided = cutting.dividedPosition();
        if (divided == null) {
            // A line on something that is not one position's own values. Not added to `made`:
            // what the partition could not read here it still could not read, and a boundary
            // answering does not answer for it (spec §example-partition).
            // Null where the quantity does not reach the line, which is the line and not one of
            // its points: three times a length is never negative, and a rule comparing one
            // against a negative draws nothing.
            // Collected rather than turned into a border here. What a border owes away from
            // its line is a run of the arrangement every rule about that quantity makes
            // together, and a border built where its comparison was read knows only its own
            // line — so a second rule over one form left the first one's run going to the end
            // of the order, past it.
            if (!Border.reaches(cutting.target(), cutting.within())) {
                raisesNoLine(accounting, behavior, plan.comparisons(), each, reads, symbols);
                return;
            }
            between.add(new LineDrawn(cutting, origin));
            List<TermPath> named = new ArrayList<>();
            mentioned(each.left(), reads, symbols, named);
            mentioned(each.right(), reads, symbols, named);
            if (named.isEmpty()) {
                return;   // a comparison about no position of the input raises nothing
            }
            // Filed at the position the reading names first, which is the one a line between two
            // would be read `on`. One comparison is one line however many positions it mentions.
            raises(accounting, behavior, plan.comparisons(), each, named.get(0),
                    comparedTerm(each, reads, symbols),
                    ComparisonSubjects.of(each, reads, symbols, null),
                    new Required.LineRead.ALineBetweenTwoPositions());
            return;
        }
        made.add(each);
        // The value a row is owed against this line, which the reading of the comparison
        // already answered. Taken off the level the rule was written with, a rule that wrote a
        // multiple of the position named a class at a number the position never holds.
        Place value = cutting.dividedValue();
        if (cutting.singles()) {
            // The value the rule names, which is where its line falls and not the value beside
            // it. A rule that names no value of the position singles nothing out here — the
            // position is divided all the same, and what divides it is the line.
            Place names = cutting.singledValue();
            if (names != null) {
                singled.add(new Guards.Singled(divided, names, origin));
            }
        } else {
            out.add(new Threshold(divided, cutting.seam(), cutting.valueBelongsBelow(), origin));
        }
        // And the line itself, where the position has no value beside it for a row to be owed
        // at. It divides the position — the classes either side are what the model tells apart
        // — and the border is drawn on the quantity the rule wrote, which can name where the
        // line falls. Left out, a rule that cuts at a third had its classes counted and nothing
        // said about its line at all.
        if (value == null && Border.reaches(cutting.target(), cutting.within())) {
            between.add(new LineDrawn(cutting, origin));
        }
        raises(accounting, behavior, plan.comparisons(), each, divided.path(), divided,
                ComparisonSubjects.of(each, reads, symbols, null),
                new Required.LineRead.ALineOnThePosition());
    }

    /** What a comparison nothing read raises, filed at the position the reading names first. */
    private static void raisesNoLine(List<Guards.AtAPosition> accounting, String behavior,
                                     ComparisonCatalog catalog, Core.Binary comparison,
                                     InputReads reads, Symbols symbols) {
        List<TermPath> named = new ArrayList<>();
        mentioned(comparison.left(), reads, symbols, named);
        mentioned(comparison.right(), reads, symbols, named);
        if (named.isEmpty()) {
            return;   // a comparison about no position of the input raises nothing about one
        }
        raises(accounting, behavior, catalog, comparison, named.get(0),
                comparedTerm(comparison, reads, symbols),
                ComparisonSubjects.of(comparison, reads, symbols, null),
                new Required.LineRead.NoLine(why(comparison, reads, symbols)));
    }

    /** The number a comparison is about, from whichever side names one. */
    static NumericTerm comparedTerm(Core.Binary comparison, InputReads reads, Symbols symbols) {
        NumericTerm left = termOf(comparison.left(), reads, symbols);
        return left != null ? left : termOf(comparison.right(), reads, symbols);
    }

    /**
     * What one comparison raises, and what the reading of it answered.
     *
     * <p>Off the comparison and not off the lines that came back. A comparison states where the
     * values stop by being written that way, and a line this could not read is exactly the case
     * where nothing answers it — walked from the lines, such a rule would be one the model never
     * wrote.
     */
    private static void raises(List<Guards.AtAPosition> out, String behavior,
                               ComparisonCatalog catalog,
                               Core.Binary comparison, TermPath at, NumericTerm term,
                               Required.ComparisonSubject of, Required.LineRead read) {
        out.add(new Guards.AtAPosition(at, term, RuleAccounting.ofComparison(
                new RuleRef.Comparison(behavior, comparison.origin()),
                souther.compiler.check.ComparisonClaim.of(comparison.op()), of, read,
                // A comparison is written rather than named, so a reader is sent where the author
                // wrote it — the comparison's own place and not the fork's. Two comparisons of one
                // condition are two rules, and cited at the `if` they were one handle twice.
                citationOf(comparison, catalog))));
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

    /**
     * The number a comparison names, which is a location's content or something taken of it.
     *
     * <p>Which of the standard library's calls count is asked of {@link NumericMeasures} rather than
     * decided here, and asked of the operation the call resolved to rather than of its spelling. The
     * argument has to be a location: {@code List.length(List.map(f, xs))} counts something no path
     * names, and a boundary on it could not be looked for in a row.
     */
    static NumericTerm termOf(Core e, InputReads reads, Symbols symbols) {
        NumericMeasures.Measured measured = NumericMeasures.takenIn(e);
        if (measured != null) {
            TermPath of = reads.pathOf(measured.of(), symbols);
            // Null where the call names a location the operation is not taken of, which a guard can
            // write and the type checker has already refused elsewhere. Answered here as "no term",
            // which is what every reader of one is ready for.
            return of == null ? null : NumericTerm.TakenOf.of(measured.operation(), of,
                    reads.read().typeAt(of, symbols), symbols);
        }
        TermPath path = reads.pathOf(e, symbols);
        return path == null ? null : new NumericTerm.ValueOf(path);
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
     * expression names is {@link #termOf}'s and which order that position is counted on is the
     * reading of the declarations' ({@link InputDomain#carrierOf}).
     *
     * <p>In particular the expression's own type is not read, here or anywhere a line is drawn. It
     * would agree wherever a rule names its positions itself and disagree wherever an operation
     * stands between them: the operands of {@code Date.daysBetween(a, b) > 10} are whole numbers
     * where its positions hold dates. Taking the order off the comparison wrote both positions back
     * as whole numbers and read them off a row as whole numbers, which agreed with itself about a
     * border nothing could meet (#1018).
     */
    static Named namedBy(Core e, InputReads reads, Symbols symbols) {
        NumericTerm term = termOf(e, reads, symbols);
        if (term == null) {
            return null;
        }
        souther.compiler.inputs.TermOrders orders = reads.read().ordersOf(term, symbols);
        return orders.answered() == null ? null : new Named(term, orders);
    }

    private GuardThresholds() {}
}
