package souther.compiler.query;

import souther.compiler.partition.Border;
import souther.compiler.partition.BorderObligationPoint;
import souther.compiler.partition.OwedPoint;
import souther.compiler.partition.PointAttribution;
import souther.compiler.partition.PointRole;

import java.util.ArrayList;
import java.util.List;

/**
 * One thing a behavior is owed a row for, at the reading of the line that a row here is composed
 * from.
 *
 * <p>What a generation composes at, and nothing else. A row is written in one behavior's terms at
 * one position, so composing one is a question about a reading — this position, this border, and
 * the value the search built there. What is owed is not: a point is owed once however many readings
 * there are, and what a finding is about, what a verdict counts and what a report prints is the
 * point across its readings ({@link BorderObligationPointAssessment}). This is the reading's side
 * of that, and a reader that took it for the account would count a line once per case a sum
 * spread it over.
 *
 * <p><b>The line and not a reading of the line's four points.</b> What is composed here is composed
 * from the line, which is what the author moved; the assessments of the border's other roles are
 * no part of this. Held here, a search would reach the points beside this one, and two of a
 * border's four can be the declarations' — so it would compose what it exists to leave to them.
 *
 * <p><b>One per obligation and not one per role.</b> A place two of this body's rules drew a line at
 * leaves a run owed to each of them; a single row may well answer both, which is what
 * {@link #oneForEachPoint} reads off this.
 *
 * <p><b>Made in one place, because the readings of it have to be of one point.</b> Where it is,
 * what is owed there and what became of it are read together, so a value assembled from parts of
 * different points would be composed at one line and labelled for another.
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
     * The places a row is composed at, over the lines this behavior's positions met.
     *
     * <p>The only place one of these is made. Which points are this behavior's to compose for is
     * the reading's own answer ({@link PointAttribution}), read here rather than decided again: a
     * row owed to the declarations that drew the line is composed for the module's account, from
     * every reading of it, and a body composing one beside that would offer the line twice.
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
     * <p>Written out because this is not a record. Two lists of these made from one reading of the
     * lines are one list, and a reader holding both is entitled to find that out.
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
        return role + " of " + line.label() + " for " + owed;
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

}
