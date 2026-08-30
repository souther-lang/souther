package souther.compiler.partition;

import souther.compiler.check.NarrowedBounds;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Requirements;
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
 * @param term    the number this axis is of: a location's own content, or something taken of it.
 *                Answered by one input position and held as such, because that is what an axis is:
 *                a run of classes over the values of a number a row can be asked for somewhere. A
 *                number read from a run of a sequence has no such place, so it draws a line without
 *                dividing anything and never arrives here
 * @param type    what stands at the position the number is read from, which is what a value read
 *                here is of. Not the term's: a string is measured at how long it is, and what
 *                stands at the location is still a string. The one thing about the location a
 *                measure needs, and nothing else about it is here — where the walk stopped, what
 *                the reading left standing and what the location is if nothing answers are true of
 *                it once however many numbers measure it, and a measure that answered them would
 *                let any reader ask a location's question through whichever number it happens to
 *                hold ({@link PositionMeasurements})
 * @param classes exclusive and exhaustive over the term's values, or empty where the model does
 *                not divide them
 * @param cuts    the values the classes meet at, each carrying every rule that drew it there
 * @param parted  where the rules part this position's values, which is not the same list. A cut is
 *                a value a row can be written against and a bound has one without parting
 *                anything; a rule that wrote a multiple of the position parts its values where the
 *                position may hold none, and has no cut. What every border on this position owes
 *                away from its line is a run of what these leave together, and the cuts alone are
 *                short of the lines that have no value
 */
public record Axis(AxisId id, NumericTerm.FromOnePosition term, Type type,
                   List<PartitionClass> classes,
                   List<Cut> cuts, List<Parting> parted, NarrowedBounds narrowed) {

    public Axis {
        classes = List.copyOf(classes);
        cuts = List.copyOf(cuts);
        parted = List.copyOf(parted);
        if (type == null) {
            throw new IllegalArgumentException("an axis of a value of nothing");
        }
        // A measure is what the rules divided a number into, cut on it, or parted it at, and one
        // with none of the three measured nothing. Such a one used to stand for a position still to
        // be answered for — which is a fact about the location and is held there
        // ({@link PositionMeasurements}), so a reader counting what a behavior is measured at was
        // counting locations among the measures.
        if (classes.isEmpty() && cuts.isEmpty() && parted.isEmpty()) {
            throw new IllegalArgumentException(
                    "`" + id + "` measures " + term + " at nothing: no class, no line and no"
                            + " parting, which is a position nothing measures and not a measure");
        }
        for (PartitionClass one : classes) {
            subjectHeld(term, one);
            // A line is a place on the number's order and falls in whichever class holds that
            // place. A class that cannot be asked about a place holds none of them, and every line
            // would fall in no class — which reads as the rules dividing the position nowhere,
            // where what happened is that a class was built without the order it sits on.
            if (!cuts.isEmpty() && !one.recognises().answersAboutAPlace()) {
                throw new IllegalArgumentException("`" + one.id() + "` cannot be asked where on "
                        + term + " it lies, and this axis has lines on it");
            }
        }
    }

    /**
     * That {@code one} is a class of the number this axis measures, which is what an axis is a run
     * of classes over.
     *
     * <p>Held where an axis is built, so that a reader crossing the classes with anything else the
     * axis holds is crossing two answers about one number. A line is a place on the term's order and
     * a class of another number is answered by reading a value of that one, so a mixed axis leaves
     * the two with nothing to compare — and what comes of asking anyway is that the class is not
     * found, which reads as the rules dividing the position nowhere.
     *
     * <p>Which number a class is of is said where the class is built and is never worked out from
     * what it means. A {@code true} is a truth wherever it stands: whether it is one of the classes
     * this position's own value is divided into is what the reading that built it decided, and an
     * axis reading that off the class would be deciding it a second time — which is how a class of
     * one position's truth would pass as a class of another's.
     */
    private static void subjectHeld(NumericTerm.FromOnePosition term, PartitionClass one) {
        if (one.of() == null) {
            throw new IllegalArgumentException("`" + one.id() + "` is a class of no measure, and"
                    + " this axis measures " + term + "; a class is put on an axis by whatever"
                    + " built it for one");
        }
        if (!one.of().equals(term)) {
            throw new IllegalArgumentException("`" + one.id() + "` is a class of " + one.of()
                    + ", and this axis measures " + term);
        }
    }

    public Axis(AxisId id, NumericTerm.FromOnePosition term, Type type,
                List<PartitionClass> classes, List<Cut> cuts) {
        this(id, term, type, classes, cuts, List.of(), NarrowedBounds.NOTHING);
    }

    /** The same position, with what a body's rules divided it into and the lines they drew. */
    public Axis carrying(List<PartitionClass> classes, List<Cut> cuts, List<Parting> parted) {
        return new Axis(id, term, type, classes, cuts, parted, narrowed);
    }

    /** Where the value this axis is about sits, which is where a row is walked to before the term is
     * read off it. Not what the axis is: two terms can be taken of one location, and {@link #id()}
     * is the one that tells them apart. */
    public TermPath path() {
        return term.position();
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

    /** Whether there is a line to draw here — classes to cover, or a boundary to reach.
     *
     * <p>A numeric newtype bounded by an invariant has the second and not the first: everything
     * outside the bound is refused at construction, so there is no other class, only an edge worth
     * a row. False where the rules part the number and the position holds no value at the parting:
     * that is a measure, and there is nothing at it for a row to be written against. */
    public boolean measurable() {
        return !classes.isEmpty() || !cuts.isEmpty();
    }

    public PartitionClass classOf(String id) {
        return classes.stream().filter(c -> c.id().equals(id)).findFirst().orElse(null);
    }
}
