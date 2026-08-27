package souther.compiler.query;

import souther.compiler.diag.SourceNameResolver;
import souther.compiler.partition.Border;
import souther.compiler.partition.BorderObligationPoint;
import souther.compiler.partition.OriginRef;
import souther.compiler.partition.OwedPoint;
import souther.compiler.partition.PointAttribution;
import souther.compiler.partition.PointRole;
import souther.compiler.source.SourceId;

import java.util.ArrayList;
import java.util.List;

/**
 * One thing a behavior is owed a row for at a line its values are held to, and what became of it.
 *
 * <p>The unit everything that measures a behavior works in: what a verdict rests on, what a finding
 * is about, and what a generator offers a row for. A behavior's account is a list of these and holds
 * nothing else, so a reader cannot ask about a point that is not the behavior's — which is the one
 * question, asked of a border's four points, that every reader used to have to remember not to put.
 *
 * <p><b>The line and not a reading of the line's four points.</b> What a report writes about one of
 * these is written from the line, which is what the author moved; the assessments of the border's
 * other roles are the block's to print and no part of this. Held here, a measure would reach the
 * points beside this one, and two of a border's four can be the declarations' — so the account would
 * hand back what it exists to keep out.
 *
 * <p><b>One per obligation and not one per role.</b> A place two of this body's rules drew a line at
 * leaves a run owed to each of them, and each is its own thing to be told about; a single row may
 * well answer both, which is a question for whoever offers rows.
 *
 * <p><b>Made in one place, because the four readings of it have to be of one point.</b> Where it is,
 * what is owed there and what became of it are read by three different readers — a report, a debt,
 * a verdict — so a value assembled from three points would be noticed by none of them.
 */
public final class OwedBoundaryPoint {

    private final Border line;
    private final PointRole role;
    private final BorderObligationPoint owed;
    private final ItemAssessment.Owed item;

    /**
     * Made from one assessed line and one of its roles, and not from four values.
     *
     * <p>A class rather than a record for that reason. The four are one point read four ways — where
     * it is, what a row there is owed for, and what became of it — and a shape anybody can fill in
     * lets a value show one line, name another line's debt and be judged by a third line's
     * measurement. Nothing downstream would notice: the three are read by three different readers.
     *
     * <p>So the assessment is what is handed in, the role picks the point out of it, and what came
     * to it is taken from there rather than passed alongside. The assessment itself is not kept —
     * an entry of a behavior's account may not reach the points beside it, which is the whole of
     * what the account is for.
     */
    private OwedBoundaryPoint(BorderAssessment at, PointRole role, BorderObligationPoint owed) {
        if (at == null || role == null || owed == null) {
            throw new IllegalArgumentException("a row owed here is owed at a point of a line, for"
                    + " something: " + owed);
        }
        // And the thing owed is a thing owed at that point of that line. Checked rather than
        // trusted: the line and the role say where a report writes this, and what is owed says what
        // a row here answers, so a value whose halves named different points would be a finding
        // about one line printed at another.
        if (!owed.line().equals(at.border().obligation()) || owed.role() != role) {
            throw new IllegalArgumentException("a point of " + at.border().label() + " at " + role
                    + " owed for something at another point: " + owed);
        }
        if (!(at.at(role) instanceof ItemAssessment.Owed measured)) {
            throw new IllegalArgumentException("a row owed at a point this border owes none at: "
                    + at.border().label() + " " + role);
        }
        this.line = at.border();
        this.role = role;
        this.owed = owed;
        this.item = measured;
    }

    /** The line, as this behavior's position met it. */
    public Border line() {
        return line;
    }

    /** Which of the border's four points this is. */
    public PointRole role() {
        return role;
    }

    /** What a row here is owed for, which several readings of the line share. */
    public BorderObligationPoint owed() {
        return owed;
    }

    /** What became of it. Owed, because a point nobody is owed a row at is no part of any account. */
    public ItemAssessment.Owed item() {
        return item;
    }

    /**
     * What this behavior is owed a row for, over the lines its positions met.
     *
     * <p>The one place a behavior's account is made, and the only place one of these is. Which
     * points are this behavior's is the reading's own answer ({@link PointAttribution}), read here
     * rather than decided again: a row owed to the declarations that drew the line is answered once
     * for the module, from every reading of it, and a behavior measured against it is weighed
     * against another behavior's rows.
     */
    public static List<OwedBoundaryPoint> across(List<BorderAssessment> lines) {
        List<OwedBoundaryPoint> out = new ArrayList<>();
        for (BorderAssessment each : lines) {
            for (PointRole role : PointRole.values()) {
                // Nothing is owed in this role at all, so neither account holds anything here and
                // the border says as much. What a report shows of such a point is the block's.
                if (!(each.at(role) instanceof ItemAssessment.Owed)) {
                    continue;
                }
                for (OwedPoint owed : each.border().owes(role)) {
                    // Every arm answered, so that whose a point is stays a question with as many
                    // answers as there are accounts. Asked as "is it this one", an arm added later
                    // would fall out of both accounts and be measured nowhere, and both producers
                    // would go on compiling.
                    switch (owed.attribution()) {
                        case PointAttribution.TheReading _ ->
                                out.add(new OwedBoundaryPoint(each, role, owed.point()));
                        // Answered once for the module, from every reading of it
                        // ({@link Adequacy.DeclaredBorders}).
                        case PointAttribution.TheDeclarations _ -> { }
                    }
                }
            }
        }
        return List.copyOf(out);
    }

    /**
     * Two of these are one where they are the same point of the same line, measured alike.
     *
     * <p>Written out because this is not a record, and because something asks: what a behavior is
     * owed is read off the lines it met, so two readings of one measurement come to the same
     * account and a reader holding both is entitled to find that out
     * ({@link BehaviorEvidence}).
     */
    @Override
    public boolean equals(Object other) {
        return other instanceof OwedBoundaryPoint that && role == that.role
                && line.equals(that.line) && owed.equals(that.owed) && item.equals(that.item);
    }

    @Override
    public int hashCode() {
        return java.util.Objects.hash(line, role, owed, item);
    }

    @Override
    public String toString() {
        return said() + " (" + role + " of " + line.label() + ")";
    }

    /**
     * A behavior's account, as a measure: what it is owed a row for, and how far the reading that
     * found the lines got.
     *
     * <p>The lines' own measure and not a second one. Which lines a behavior's positions meet is
     * what the reading of them came to, and an account made from a reading that did not run out is
     * an account that may be short of entries — so what weakened the reading weakens this, and a
     * verdict reading the entries alone would take a behavior whose lines nobody could derive for
     * one with nothing to answer for.
     *
     * <p>Complete and empty is a different answer from either: the lines were read to the end, and
     * every point of them is owed to the declarations that drew them.
     */
    public static Measure<List<OwedBoundaryPoint>> accountOf(
            Measure<List<BorderAssessment>> lines) {
        return lines.readAs(OwedBoundaryPoint::across);
    }

    /**
     * The places a row is composed at, one per point of a line rather than one per thing owed there.
     *
     * <p><b>Its own type, because it is not the account.</b> What is dropped getting here is
     * {@link OwedBoundaryPoint#owed()} — the thing owed, which is what tells two obligations at one
     * point apart — so a reader whose unit is the obligation and one whose unit is the row want
     * different lists. Handed back as the account's own type, either could be passed where the other
     * was meant, and the one that wanted the obligations would silently be given as many as there
     * are points.
     *
     * @param at one entry per point, each naming one of the things owed there. Everything a row is
     *           composed and labelled from — the line, the role and what was measured — is the same
     *           at all of them, which is what makes one value enough
     */
    public record WhereARowIsComposed(List<OwedBoundaryPoint> at) {

        public WhereARowIsComposed {
            at = List.copyOf(at);
        }
    }

    /**
     * The points this run was asked for a row at, which is not everything that is owed one.
     *
     * <p><b>Its own type, because it is not the account either.</b> What is owed is what the lines
     * ask of the rows; what a generation is asked for is that less what the measurement has already
     * settled — a point a written row stands at, and a point nothing measured. Read as the account,
     * a run counts work nobody is owed: a candidate that stands where a written row already stands
     * is the only offer for a point in nobody's way, so nothing may drop it and it goes out beside
     * the row that made it unnecessary.
     *
     * @param at the points, in the account's own order
     */
    public record WhereARowWasAskedFor(List<OwedBoundaryPoint> at) {

        public WhereARowWasAskedFor {
            at = List.copyOf(at);
        }
    }

    /**
     * The account read as what this run has to offer a row for.
     *
     * <p>Asked of {@link ItemAssessment.Owed#worthSearching()} and of nothing else. Whether a
     * candidate here would tell anybody anything is the measurement's answer — it is what the search
     * itself is gated on — and a second reading of it would be a second answer to one question,
     * free to disagree the day either moved.
     */
    public static WhereARowWasAskedFor askedForARow(List<OwedBoundaryPoint> account) {
        List<OwedBoundaryPoint> at = new ArrayList<>();
        for (OwedBoundaryPoint each : account) {
            if (each.item().worthSearching()) {
                at.add(each);
            }
        }
        return new WhereARowWasAskedFor(at);
    }

    /**
     * The account read as the places a row is composed at.
     *
     * <p>A row stands at a point of a line, and what a row there shows answers everything a row
     * there is owed for — so a place two of this body's rules drew a line at is two things to be
     * told about and one value to compose. Walked as the obligations, a search that composed one
     * value would offer it twice.
     */
    public static WhereARowIsComposed oneForEachPoint(List<OwedBoundaryPoint> account) {
        List<OwedBoundaryPoint> at = new ArrayList<>();
        for (OwedBoundaryPoint each : account) {
            if (at.stream().noneMatch(
                    seen -> seen.role() == each.role() && seen.line().equals(each.line()))) {
                at.add(each);
            }
        }
        return new WhereARowIsComposed(at);
    }

    /** The position the line is on, as a report names it. */
    public String axis() {
        return line.axis();
    }

    /** What this asks of a row, as a report writes it. */
    public String asked() {
        return line.operator(role) + " " + line.against(role);
    }

    /** What the point is against. */
    public String against() {
        return line.against(role);
    }

    /** The class a row here falls in, as one line of a class list is written. The line's own
     *  answer, so that a finding about this point and the block that shows the line name it
     *  alike. */
    public String said() {
        return line.said(role);
    }

    /** The rule that drew the line, as a report about {@code sectionSource} writes it. */
    public String describe(SourceNameResolver names, SourceId sectionSource) {
        return line.describe(names, sectionSource);
    }

    /** The rule as this reading met it, for a reader that renders it rather than printing what
     *  {@link #describe} would. */
    public OriginRef origin() {
        return line.origin();
    }
}
