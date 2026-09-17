package souther.compiler.query;

import souther.compiler.check.RuleCitation;
import souther.compiler.check.RuleCitations;
import souther.compiler.partition.Border;
import souther.compiler.partition.Demand;
import souther.compiler.partition.BoundaryTarget;
import souther.compiler.partition.DomainPoint;
import souther.compiler.partition.LineOrigin;
import souther.compiler.partition.PointRole;
import souther.compiler.publish.PublishedRuleHandle;
import souther.compiler.publish.PublishedSentence;

import java.util.Map;
import java.util.Set;

/**
 * Everything known about one reading of one border: the line as this position met it, and what
 * became of each of its coverage items at this reading.
 *
 * <p>One of these per border, made in one place. It is the occurrence: where a row can be written
 * and what the search there came to, which is what a block that shows a border whole prints and
 * what a generation composes from. What is owed is not here — a line is owed once however many
 * positions read it — and what a finding is about, what a verdict counts and what a report marks is
 * the point across its readings ({@link BorderObligationPointAssessment}), which is gathered from
 * these and never read off one of them.
 *
 * <p><b>And what the rows leave standing beside the line.</b> The points say whether a row stands
 * where the line is and beside it, which is what shows a line has not moved; what shows it has not
 * turned is that no other line the model's own weights put one step away answers alike at every row
 * ({@link AnotherLineTheRowsAllow}). Both come off this one reading of these rows, so what a build
 * refuses over is one measurement read two ways rather than two measurements made to different
 * rules.
 *
 * <p><b>And what a search for a row that would tell them apart came to.</b> Beside the line the rows
 * allow rather than inside it: which lines these rows leave standing is what this compilation
 * measured, and whether a row can be composed at one of the inputs that would settle it is work
 * somebody asked for. Written into the measurement, a reading nobody asked to compose for would
 * have had to carry a search that never ran.
 *
 * <p><b>Total over the points its border has, the way that border is.</b> A border answers at every
 * point its rule gives it and so does this, so a reader asking what one of them came to is never
 * answered by an entry that is not there. Which of the four each point is is the line's answer
 * ({@link Border#roleOf}) and is asked of it rather than kept here: a role is what a point is and
 * two points of one border can be the same one, so a measure keyed on the role would hold one entry
 * where there are two.
 */
public record BorderAssessment(Border border, Map<DomainPoint, ItemAssessment> items,
                               AnotherLineTheRowsAllow beside, ARowTellingTheLinesApart toldApart)
        implements RuleCitations {

    /** One reading of a line, before anybody asked for a row that would tell it from the lines
     *  beside it. */
    public BorderAssessment(Border border, Map<DomainPoint, ItemAssessment> items,
                            AnotherLineTheRowsAllow beside) {
        this(border, items, beside, ARowTellingTheLinesApart.notAsked());
    }

    /**
     * The one handle this reading holds, which is the one the rule that drew the line was cited by.
     *
     * <p>One, because a reading is of one line and a line is drawn by one rule. The several a debt
     * holds are the several readings of it gathered ({@link BorderObligationPointAssessment}), and
     * are that value's answer rather than this one's.
     */
    @Override
    public Set<RuleCitation> ruleCitations() {
        return Set.of(origin().cited());
    }

    /**
     * What holding this line against the lines beside it went without, where it came back unsettled.
     *
     * <p>Empty for every settled answer, whichever way it settled and however few rows it took. A
     * walk short of a row that left no line standing has established that, because reading more
     * rows leaves fewer lines standing and never more — so a measure weakened by every partial walk
     * would hold a verdict open over a question that was answered.
     *
     * <p>Made here because the facts are about this border and the answer does not hold one. A
     * reading that came to nothing and readings nobody made are the same two facts the points of
     * this border carry, said in the same words, so a reader is told them once however many
     * questions over these rows went without them.
     */
    public WeakeningSet besideWeakening() {
        if (!(beside instanceof AnotherLineTheRowsAllow.CouldNotTell(var why))) {
            return WeakeningSet.none();
        }
        return switch (why) {
            case AnotherLineTheRowsAllow.Unsettled.RowsIncomplete(ReadingReasons met) -> {
                WeakeningSet out = WeakeningSet.none();
                for (souther.compiler.partition.ReadingGap gap : met.eachKindOnce().written()) {
                    out = out.union(
                            WeakeningSet.of(new Weakening.BorderValueUnreadable(border, gap)));
                }
                yield met.tried() instanceof souther.compiler.partition.StandingAtAPoint
                        .ReadingsTried.StoppedAtTheLimit(int limit)
                        ? out.union(WeakeningSet.of(
                                new Weakening.BorderReadingsNotExhausted(border, limit)))
                        : out;
            }
            // The reading's own, which is what a measure over these lines is worth.
            case AnotherLineTheRowsAllow.Unsettled.TheRowsWereNotRead(var as) -> as.weakening();
            case AnotherLineTheRowsAllow.Unsettled.TheRowsAreAllOnOneSide _ ->
                    WeakeningSet.of(new Weakening.ABorderNotHeldAgainstTheLinesBesideIt(border,
                            Weakening.ABorderNotHeldAgainstTheLinesBesideIt.Why
                                    .THE_ROWS_ARE_ALL_ON_ONE_SIDE));
            case AnotherLineTheRowsAllow.Unsettled.NoStrategyForIt _ ->
                    WeakeningSet.of(new Weakening.ABorderNotHeldAgainstTheLinesBesideIt(border,
                            Weakening.ABorderNotHeldAgainstTheLinesBesideIt.Why
                                    .NO_STRATEGY_FOR_THE_RULE));
            // The two lines part company only where nothing here can say a row arrives, which is a
            // question about the way to the border rather than about the rows.
            case AnotherLineTheRowsAllow.Unsettled.NoReachableDistinguisher _ ->
                    WeakeningSet.of(new Weakening.ABorderNotHeldAgainstTheLinesBesideIt(border,
                            Weakening.ABorderNotHeldAgainstTheLinesBesideIt.Why
                                    .NO_REACHABLE_DISTINGUISHER));
            case AnotherLineTheRowsAllow.Unsettled.TheRunsWereNotWatched _ ->
                    WeakeningSet.of(new Weakening.ABorderNotHeldAgainstTheLinesBesideIt(border,
                            Weakening.ABorderNotHeldAgainstTheLinesBesideIt.Why
                                    .NOTHING_WATCHED_THE_RUNS));
        };
    }

    /**
     * Whether holding this line against the lines beside it came to an answer.
     *
     * <p>Which is not whether a line was found. A border no line beside it survives and a border
     * with one named are both settled; a border the question could not be put of is not, and a
     * border with no line beside it at all was never a question.
     */
    public boolean besideSettled() {
        return !(beside instanceof AnotherLineTheRowsAllow.CouldNotTell);
    }

    public BorderAssessment {
        if (beside == null) {
            throw new IllegalArgumentException("a border says what the rows leave standing beside"
                    + " it, and a border that was not asked says that: " + border);
        }
        if (toldApart == null) {
            throw new IllegalArgumentException("a reading says what a search for a row telling this"
                    + " line from the ones beside it came to, and a reading nobody asked says"
                    + " that: " + border);
        }
        if (items == null || !items.keySet().equals(border.answers().keySet())) {
            throw new IllegalArgumentException(
                    "a border assessed at some of its points and not others: " + items);
        }
        // And each of them assessed as what the border says it owes. The two records answer the same
        // question about the same point — what is owed there — and holding them apart without
        // holding them together leaves a point the rules refuse carrying a row that is at it. What a
        // report prints and what a build refuses over read one of the two, so they may not disagree.
        for (DomainPoint point : items.keySet()) {
            agrees(border, point, items.get(point));
        }
        items = java.util.Collections.unmodifiableMap(new java.util.LinkedHashMap<>(items));
    }

    /**
     * That an item answers for the demand its border makes in that role.
     *
     * <p>Checked rather than derived, because the two are made by different things: the border says
     * what is owed and the measure says what became of it, and a measure that answered about a role
     * it had not been told about is the two coming apart. Deriving the item from the demand instead
     * would put the measure's answer where its question is.
     */
    private static void agrees(Border border, DomainPoint point, ItemAssessment item) {
        Demand demand = border.demand(point);
        switch (item) {
            case null -> throw new IllegalArgumentException(
                    "a border with a point it names and does not assess: " + point);
            case ItemAssessment.NotOwed not -> {
                if (!(demand instanceof Demand.NotOwed owed) || owed.reason() != not.reason()) {
                    throw new IllegalArgumentException("the " + point + " of " + border.label()
                            + " is assessed as not owed for " + not.reason()
                            + ", and its border says " + demand);
                }
            }
            case ItemAssessment.Owed owed -> {
                if (!(demand instanceof Demand.Owed asked)
                        || !asked.criterion().sameAs(owed.criterion())) {
                    throw new IllegalArgumentException("the " + point + " of " + border.label()
                            + " is assessed against " + owed.criterion()
                            + ", and its border asks " + demand);
                }
            }
        }
    }

    /** What became of one point. Never null. */
    public ItemAssessment at(DomainPoint point) {
        return items.get(point);
    }

    /**
     * The same of the one point playing {@code role}.
     *
     * <p>For a reader holding a classification, which is what a person asking about a border does.
     * The line refuses where two of its points play the role ({@link Border#theOne}), so this is a
     * question about a line whose shape the caller has established and never a way to key on the
     * role.
     */
    public ItemAssessment at(PointRole role) {
        return at(border.theOne(role));
    }

    /** The measured half of the one point playing {@code role}, or null where no row is owed
     *  there. */
    public ItemAssessment.Owed owedAt(PointRole role) {
        return owedAt(border.theOne(role));
    }

    /**
     * The measured half of one role, or null where no row is owed there.
     *
     * <p>For a reader that has already established which role it is asking about. Null here is a
     * reading and not a state anything can be built in: what is owed is settled where the border is
     * made, and nothing can produce an item that is both refused by the rules and sat on by a row.
     */
    public ItemAssessment.Owed owedAt(DomainPoint point) {
        return at(point) instanceof ItemAssessment.Owed owed ? owed : null;
    }

    /** The position this border is on, as a report names it. The line's own answer, so that a point
     *  taken out of this and the block printed round it name it alike. */
    public String axis() {
        return border.axis();
    }

    /** Which shape this line has, which is what says how to read what each item asks for. */
    public BoundaryTarget.Shape shape() {
        return border.cut().shape();
    }

    /** The rule that drew the line, as what a report writes about it, with {@code places} asked
     *  where the rule is one found by where it is written. */
    public PublishedSentence describe(PublishedRuleHandle.WhereARuleIs places) {
        return border.describe(places);
    }

    /**
     * The rule as this reading met it, for a reader that renders it rather than printing what
     * {@link #describe} would.
     *
     * <p>An {@link LineOrigin} and not a {@link souther.compiler.check.RuleRef}, which is why it is
     * not called the rule. Which rule of the model this came from is
     * {@link souther.compiler.partition.BorderObligationId#provenance()}, the same value however
     * many lines the rule drew; what a row is owed for is
     * {@link souther.compiler.partition.Border#obligation()}. Named the rule, the first two were one
     * word, and a caller wanting either reached for whichever this happened to be.
     */
    public LineOrigin origin() {
        return border.origin();
    }

    /** Where the line is, as a report names it. */
    public String label() {
        return border.label();
    }

    /** What a row at one point of it would be written as, or null where none is owed there. */
    public String label(DomainPoint point) {
        return border.label(point);
    }

    /** How one point relates a row's value to what it is against, or null where none is owed. */
    public String operator(DomainPoint point) {
        return border.operator(point);
    }

    /** What that point is against, or null where none is owed. */
    public String against(DomainPoint point) {
        return border.against(point);
    }

    /** The same three of the one point playing {@code role}. */
    public String label(PointRole role) {
        return label(border.theOne(role));
    }

    public String operator(PointRole role) {
        return operator(border.theOne(role));
    }

    public String against(PointRole role) {
        return against(border.theOne(role));
    }

    /** The left of the {@code left = right} a report names this line by. */
    public String left() {
        return border.cut().left();
    }

    /** The right of it, which for a line between two positions is the other position. */
    public String value() {
        return border.cut().right();
    }

    /**
     * One coverage item of one border, for a reader that walks the items rather than the borders.
     *
     * <p>One place turns a border into its items, so that a reader walking them is never short of
     * one: all four are here, and a role the rule owes nothing in says so rather than being left
     * out. What is <em>not</em> read off this list is what anybody is owed — a count, a finding and
     * a verdict work in obligations, which are what the readings of a line come to together
     * ({@link BorderObligationPointAssessment}), and a line is owed once however many positions
     * read it. This list has one entry per reading of each point, so anything counting it counts
     * the walk.
     */
    public record Point(BorderAssessment border, DomainPoint at, ItemAssessment item) {

        /** Which of the four this is, which the line it is a point of answers. */
        public PointRole role() {
            return border.border().roleOf(at);
        }

        /** What a row here would be written as, or null where none is owed. */
        public String label() {
            return border.label(at);
        }

        /** What this asks of a row, as a report writes it, or null where none is owed. */
        public String asked() {
            return border.operator(at) == null ? null
                    : border.operator(at) + " " + border.against(at);
        }

        /** What the point is against, or null where none is owed. */
        public String against() {
            return border.against(at);
        }

        /** The class a row here falls in, as one line of a class list is written. The line's own
         *  answer, so that a point taken out of this and one of a behavior's account say it
         *  alike. */
        public String said() {
            return border.border().said(at);
        }

        /** The measured half, or null where no row is owed here. */
        public ItemAssessment.Owed owed() {
            return item instanceof ItemAssessment.Owed owed ? owed : null;
        }
    }

    /** Every one of this border's items, in the order its points are in. */
    public java.util.List<Point> points() {
        return items.keySet().stream().map(point -> new Point(this, point, at(point))).toList();
    }

    /** The same over a list of borders. */
    public static java.util.List<Point> pointsOf(java.util.List<BorderAssessment> borders) {
        return borders.stream().flatMap(each -> each.points().stream()).toList();
    }

    /**
     * The same point of the same line, in another reading of one behavior's lines.
     *
     * <p>For a reader holding a later assessment than the one it was handed. The lines of a behavior
     * are measured once and searched afterwards, so a finding made from the measurement names a
     * point that the search has more to say about, and this is how the second is asked for the first.
     *
     * <p>Found by the border itself, which is a value, and by the role. The four fields a finding
     * used to carry instead — the axis, the value, the rule and the role — did not identify a point:
     * several rules can draw a line at one value, so a reader matching those answered with whichever
     * assessment came first. Two lines here that are equal are the same line, and this refuses to
     * choose between two of them rather than taking one.
     *
     * @throws IllegalStateException where no line here is that one, or where more than one is
     */
    public static ItemAssessment owedAt(java.util.List<BorderAssessment> lines, Border line,
                                        DomainPoint point) {
        ItemAssessment found = null;
        for (BorderAssessment each : lines) {
            if (!each.border().sameReadingAs(line)) {
                continue;
            }
            if (found != null) {
                throw new IllegalStateException(
                        "one behavior's lines hold " + line.label() + " twice, so the "
                                + point + " of it is two points");
            }
            found = each.at(point);
        }
        if (found == null) {
            throw new IllegalStateException("no line here is " + line.label()
                    + ", so its " + point + " is not one of these");
        }
        return found;
    }

    /** The points a row is owed at, which is what a coverage count is over. */
    public java.util.List<DomainPoint> owed() {
        return items.keySet().stream().filter(point -> at(point).owed()).toList();
    }

    /** The points the model's own rules discharged, which a report counts as excluded rather than as
     *  items nobody has got to. */
    public java.util.List<DomainPoint> excluded() {
        return items.keySet().stream()
                .filter(point -> border.demand(point).excluded()).toList();
    }
}
