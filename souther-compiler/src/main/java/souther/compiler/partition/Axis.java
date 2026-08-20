package souther.compiler.partition;

import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.StructuralInspection;
import souther.compiler.inputs.TermPath;
import souther.compiler.types.Type;
import souther.compiler.check.RuleAccounting;

import java.util.Collection;
import java.util.List;
import java.util.Set;

/**
 * One input position that a model distinguishes values at, and the classes it distinguishes them into.
 *
 * <p>The model's own distinctions, not invented ones. A type with two cases has two classes; a
 * {@code guard}'s comparison divides what a position holds into the two sides it treats differently.
 * A position the model says nothing about — a plain {@code String}, an {@code Int} with no invariant
 * — has no classes, and that is reported as not derivable rather than filled in with values nobody
 * asked for. The choice matters: a made-up partition measures a rule the model does not have, and
 * reports coverage of it.
 *
 * <p>A bound is not one of them. An invariant's bound gives a boundary and no partition: everything
 * outside it is refused at construction, so there is no class on the far side to cover (ADR-0090),
 * and what such a position gets is {@link #cuts} and no classes — which is what {@link #measurable}
 * is for. What a bound does contribute to a partition is the range the classes are clipped to: the
 * two either side of a {@code guard} at 50 run from the bound and not from the type's own ends.
 *
 * @param term     the number this axis is of: a location's own content, or something taken of it
 * @param classes  exclusive and exhaustive over the term's values, or empty where the model does
 *                 not divide them
 * @param cuts     the values the classes meet at, each carrying every rule that drew it there
 * @param pending  where nothing has answered for this position yet, what the structural reading
 *                 found — and so what this position is left with if nothing else answers. Null on
 *                 an axis that already has evidence, which needs no fallback.
 *
 *                 <p>Carried here rather than beside: the reason and the position it is about are
 *                 one fact, and holding them in two lists joined afterwards by the spelling of a
 *                 path is how a reason came to be recovered by string match. A reason travels with
 *                 the position or it is a reason about whatever the strings happened to pair it
 *                 with.
 * @param unanswered the questions the rules written about this position raise that nothing
 *                 answered, each naming the rule that raised it. Carried because it qualifies the
 *                 classes and nothing else says it: a rule nothing took in may yet refuse a value a
 *                 class holds, so {@link #classes} is the denominator the model states and not one
 *                 every class of which is known to be inhabited.
 *
 *                 <p>The questions and not a reading's account of itself. The reading that turns
 *                 clauses into sets of values has no word for a range and is short of the rules at
 *                 every numeric position an invariant bounds, while two other readings have those
 *                 rules whole — so a report written off that reading says a model was not read on
 *                 the strength of a fact about this compiler (issue #842)
 * @param rulesNotReached whether the walk reached the rules written about this position at all.
 *                 Beside the questions and not among them: a position whose rules were never
 *                 enumerated raises no question and is not one whose rules were all accounted for,
 *                 and an empty list says the second (issue #791)
 * @param unread   a rule about this position's own values that the local reading did not take in,
 *                 or null where it read them all. Carried for the same reason {@link #pending} is,
 *                 and kept apart from it because the two are lifted by different work and one
 *                 outranks the other: where the walk could not reach into what the position holds,
 *                 a rule about what is inside describes that same stop from the other end
 */
public record Axis(AxisId id, NumericTerm term, Type type, List<PartitionClass> classes,
                   List<Cut> cuts, List<RuleAccounting.Unanswered> unanswered,
                   boolean rulesNotReached,
                   StructuralInspection.Pending pending, BlockReason.Stopped unread) {

    public Axis {
        classes = List.copyOf(classes);
        cuts = List.copyOf(cuts);
        if (unanswered == null) {
            throw new IllegalArgumentException(
                    "a position with no account of what its rules leave standing");
        }
        unanswered = List.copyOf(unanswered);
    }

    public Axis(AxisId id, NumericTerm term, Type type, List<PartitionClass> classes,
                List<Cut> cuts) {
        this(id, term, type, classes, cuts, List.of(), false, null, null);
    }

    /**
     * A position nothing has answered for yet, and what the readings of it found.
     *
     * <p>Not a position the model does not divide. A rule a body writes may still draw a line on it,
     * and only where none does is what was found here what a report says — an absence where every
     * reading ran to the end and found nothing, and what stopped one where it did not.
     */
    public static Axis pendingAt(AxisId id, NumericTerm term, Type type,
                                 List<RuleAccounting.Unanswered> unanswered,
                                 boolean rulesNotReached,
                                 StructuralInspection.Pending found, BlockReason.Stopped unread) {
        return new Axis(id, term, type, List.of(), List.of(), unanswered, rulesNotReached, found,
                unread);
    }

    /**
     * The same position, measured at another number.
     *
     * <p>A transition rather than a constructor at the call site. What a body's rules add is a term,
     * classes and cuts; everything else about the position was settled by the reading that made
     * this one, and a caller rebuilding an axis from its parts drops whatever it did not think to
     * name. What went that way was {@link #pending}: a position whose elements could not be reached
     * came back out of the second phase with nothing to say it had ever stopped, and was reported
     * as one the model divides no way.
     */
    public Axis measuredAt(AxisId id, NumericTerm term) {
        return new Axis(id, term, type, classes, cuts, unanswered, rulesNotReached, pending,
                unread);
    }

    /** The same position, with what a body's rules divided it into and the lines they drew. */
    public Axis carrying(List<PartitionClass> classes, List<Cut> cuts) {
        return new Axis(id, term, type, classes, cuts, unanswered, rulesNotReached, pending,
                unread);
    }

    /** Where the value this axis is about sits, which is where a row is walked to before the term is
     * read off it. Not what the axis is: two terms can be taken of one location, and {@link #id()}
     * is the one that tells them apart. */
    public TermPath path() {
        return term.path();
    }

    /**
     * The classes a row can be written at.
     *
     * <p>The one denominator. What a report counts, what a pair space is the product of, and what
     * the generator offers rows for all come from here — three derivations of the same universe are
     * three chances to disagree about it, which is how a class nothing can reach came to be asked
     * for by three measures at once.
     *
     * <p>Nothing a body writes narrows this. A case an arm declares cannot arrive is a claim about
     * the same position, and what became of the claim is said beside the report rather than taken
     * out of the count here — a claim the rules bear out has already left, because the reading these
     * classes come from is what took it out.
     */
    /** Whether the model divides this position into classes to cover. */
    public boolean derivable() {
        return !classes.isEmpty();
    }

    /** Whether there is anything here to measure at all — classes to cover, or a boundary to reach.
     * A numeric newtype bounded by an invariant has the second and not the first: everything outside
     * the bound is refused at construction, so there is no other class, only an edge worth a row. */
    public boolean measurable() {
        return !classes.isEmpty() || !cuts.isEmpty();
    }

    public PartitionClass classOf(String id) {
        return classes.stream().filter(c -> c.id().equals(id)).findFirst().orElse(null);
    }
}
