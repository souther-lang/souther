package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Requirements;
import souther.compiler.inputs.StructuralInspection;
import souther.compiler.inputs.TermPath;
import souther.compiler.types.Type;

import java.util.List;

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
 * <p>{@link #classes} is the one denominator. What a report counts, what a pair space is the
 * product of, and what the generator offers rows for all come from there — three derivations of the
 * same universe are three chances to disagree about it, which is how a class nothing can reach came
 * to be asked for by three measures at once. Nothing a body writes narrows it: a case an arm
 * declares cannot arrive is a claim about the same position, and what became of the claim is said
 * beside the report rather than taken out of the count — a claim the rules bear out has already
 * left, because the reading these classes come from is what took it out.
 *
 * @param term     the number this axis is of: a location's own content, or something taken of it
 * @param classes  exclusive and exhaustive over the term's values, or empty where the model does
 *                 not divide them
 * @param cuts     the values the classes meet at, each carrying every rule that drew it there
 * @param parted   where the rules part this position's values, which is not the same list. A cut is
 *                 a value a row can be written against and a bound has one without parting
 *                 anything; a rule that wrote a multiple of the position parts its values where the
 *                 position may hold none, and has no cut. What every border on this position owes
 *                 away from its line is a run of what these leave together, so a border built from
 *                 the cuts alone read its two sides past the lines that have no value (issue #880)
 * @param pending  where nothing has answered for this position yet, what the structural reading
 *                 found — and so what this position is left with if nothing else answers. Null on
 *                 an axis that already has evidence, which needs no fallback.
 *
 *                 <p>Carried here rather than beside: the reason and the position it is about are
 *                 one fact, and holding them in two lists joined afterwards by the spelling of a
 *                 path is how a reason came to be recovered by string match. A reason travels with
 *                 the position or it is a reason about whatever the strings happened to pair it
 *                 with.
 * @param residue  what the reading of this position left behind that nothing later takes away: the
 *                 rules it was owed and did not reach, and whether the walk could go into what it
 *                 holds. Beside the questions and not among them — a position whose rules were never
 *                 enumerated raises no question and is not one whose rules were all accounted for,
 *                 and an empty list says the second (issue #791).
 *
 *                 <p>Apart from {@link #pending} because the two do not live as long. A position a
 *                 body's rule divides keeps no continuation to be pending on, and was still never
 *                 entered; read off the continuation, that stop went unsaid (issue #1084)
 * @param leftWith what the position is left with where the local reading gave it no axis, or null
 *                 where nothing is. Which of the two it is comes with it: a reading stopped, or a
 *                 rule was read to the end and draws no line. Carried for the same reason
 *                 {@link #pending} is, and kept apart from it because the two are lifted by
 *                 different work and one outranks the other — where the walk could not reach into
 *                 what the position holds, a rule about what is inside describes that same stop
 *                 from the other end
 */
public record Axis(AxisId id, NumericTerm term, Type type, List<PartitionClass> classes,
                   List<Cut> cuts, List<Parting> parted, ReadingResidue residue,
                   StructuralInspection.Continuation pending, LeftAtThePosition leftWith) {

    public Axis {
        classes = List.copyOf(classes);
        cuts = List.copyOf(cuts);
        parted = List.copyOf(parted);
        if (residue == null) {
            throw new IllegalArgumentException(
                    "an axis with no account of what its reading came to");
        }
    }

    public Axis(AxisId id, NumericTerm term, Type type, List<PartitionClass> classes,
                List<Cut> cuts) {
        this(id, term, type, classes, cuts, List.of(), ReadingResidue.NOTHING, null, null);
    }

    /**
     * A position nothing has answered for yet, and what the readings of it found.
     *
     * <p>Not a position the model does not divide. A rule a body writes may still draw a line on it,
     * and only where none does is what was found here what a report says — an absence where every
     * reading ran to the end and found nothing, and what stopped one where it did not.
     */
    public static Axis pendingAt(AxisId id, NumericTerm term, Type type, ReadingResidue residue,
                                 StructuralInspection.Continuation found,
                                 LeftAtThePosition leftWith) {
        return new Axis(id, term, type, List.of(), List.of(), List.of(),
                residue, found, leftWith);
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
        return new Axis(id, term, type, classes, cuts, parted, residue, pending, leftWith);
    }

    /** The same position, with what a body's rules divided it into and the lines they drew. */
    public Axis carrying(List<PartitionClass> classes, List<Cut> cuts, List<Parting> parted) {
        return new Axis(id, term, type, classes, cuts, parted, residue, pending, leftWith);
    }

    /** Where the value this axis is about sits, which is where a row is walked to before the term is
     * read off it. Not what the axis is: two terms can be taken of one location, and {@link #id()}
     * is the one that tells them apart. */
    public TermPath path() {
        return term.path();
    }

    /**
     * What a row has to be for this position to exist in it at all.
     *
     * <p>Read off the path and kept nowhere else. A position under a narrowing requires it by being
     * there — {@code query@GlobalQuery.tag} says that {@code query} is a {@code GlobalQuery} and
     * says it completely — so an account of it beside the path would be two readings of one fact.
     */
    public Requirements requirements() {
        return path().requirements();
    }

    /**
     * The same, for a row sitting in {@code cls} here.
     *
     * <p>Both halves and neither standing for the other. A class of a sum states a narrowing by
     * being the class it is, and the position it is a class of may itself be under one — so what a
     * row at this class has to be is what the position requires and what the class selects,
     * together.
     */
    public Requirements requiring(PartitionClass cls) {
        return requirements().and(path(), cls == null ? null : cls.selects());
    }

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
