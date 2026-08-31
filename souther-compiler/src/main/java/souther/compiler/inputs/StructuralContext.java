package souther.compiler.inputs;

import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

/**
 * What a question about an input assumes stands: the narrowings it selects, and the sequences it
 * needs to hold an element.
 *
 * <p>Every position of an input exists under conditions. A field of a case is there where the value
 * turned out to be that case; a field of an element is there where the sequence holds one. So a
 * question naming positions is a question asked of the rows that meet those conditions, and which
 * rules reach it is settled by that and by nothing else ({@link #holds}).
 *
 * <p><b>Structural and nothing else.</b> It records the refinements selected and the containing
 * sequences required to hold an element. It holds no numeric constraint, no fixed value and no
 * assumption: <em>those are interpreted under this context, not made part of it.</em> Which is what
 * the name is for. Called a context outright it would be where the next reader files a fixed value —
 * a fixed value being part of the context of a question in every sense but this one — and the line
 * this draws between what a reading assumes exists and what it then says about it would have been
 * rubbed out from the left.
 *
 * <p><b>One owner, because one place has to decide it.</b> Everything asked of a reading of an
 * input — where a form runs, what a fixing settles, what a condition takes in, whether anything is
 * left — is asked under one of these, assembled the same way from the same three sources. Worked out
 * per question instead, each reader would look at a path and decide for itself that a case was
 * wanted, and the readers would come apart one at a time.
 */
record StructuralContext(Requirements refinements, Set<TermPath> nonEmptySequences) {

    /** A question that assumes nothing: the parameters, and whatever stands under no condition. */
    static final StructuralContext NONE = new StructuralContext(Requirements.NONE, Set.of());

    StructuralContext {
        nonEmptySequences = Set.copyOf(nonEmptySequences);
    }

    /**
     * What naming {@code path} assumes.
     *
     * <p>Both halves read off the path, which is where they are already kept:
     * {@link TermPath#requirements} says which narrowings were taken to get here, and
     * {@link TermPath#sequencesContainingIt} says which containers have to hold something for this
     * to be anywhere. Kept beside a path instead, a position would carry a second account of what it
     * already says.
     */
    static StructuralContext of(TermPath path) {
        return new StructuralContext(path.requirements(),
                new LinkedHashSet<>(path.sequencesContainingIt()));
    }

    /**
     * Both, or the position they disagree about.
     *
     * <p>Refinements are compared by {@link Requirements#merge} and by nothing written here: whether
     * two narrowings hold of one value is that type's question, asked by everything that decides
     * whether two positions can be in one row. Sequences only accumulate — needing one to hold an
     * element and needing another to hold one are never at odds.
     */
    Merge merge(StructuralContext other) {
        return switch (refinements.merge(other.refinements)) {
            case Requirements.Merge.Conflict it -> new Merge.Disagreeing(it);
            case Requirements.Merge.Merged it -> {
                Set<TermPath> both = new LinkedHashSet<>(nonEmptySequences);
                both.addAll(other.nonEmptySequences);
                yield new Merge.Together(new StructuralContext(it.requirements(), both));
            }
        };
    }

    /** What came of putting two of them together. */
    sealed interface Merge {

        /** They hold of one value, and this is what such a value has to be. */
        record Together(StructuralContext context) implements Merge {}

        /**
         * They do not, and this is the position that cannot be both.
         *
         * <p>Carried as the refinements' own answer. What a caller does about it differs — a
         * question about a quantity of no value is refused, and two fixings that cannot both hold
         * are an emptiness — and neither of those readings belongs to the disagreement itself.
         */
        record Disagreeing(Requirements.Merge.Conflict why) implements Merge {}
    }

    /**
     * The same, with the value at {@code at} settled as {@code branch} as well.
     *
     * <p>What a reader walking the alternatives of a sum asks about one of them. A narrowing already
     * settled here is not settled again: {@link Requirements#and} refuses a second answer at one
     * position, which is a caller asking about a case it has already ruled out.
     */
    StructuralContext and(TermPath at, Refinement branch) {
        return new StructuralContext(refinements.and(at, branch), nonEmptySequences);
    }

    /**
     * The same, with {@code sequence} required to hold an element as well.
     *
     * <p>What a reader asking whether anything can stand inside a container assumes while it asks.
     * A container that may be empty is a value whatever is true of what it would hold, so the
     * question is only ever asked under this.
     */
    StructuralContext holding(TermPath sequence) {
        Set<TermPath> more = new LinkedHashSet<>(nonEmptySequences);
        more.add(sequence);
        return new StructuralContext(refinements, more);
    }

    /**
     * Whether everything {@code other} assumes is already assumed here.
     *
     * <p>What says a position exists in the values this describes: a sum inside a case is a place to
     * ask about only once the value is that case, and asking about it under a context that has not
     * settled the case would be walking alternatives of a sum that stands nowhere.
     */
    boolean covers(StructuralContext other) {
        for (Map.Entry<TermPath, Refinement> each : other.refinements.refinements().entrySet()) {
            if (!each.getValue().equals(refinements.at(each.getKey()))) {
                return false;
            }
        }
        return nonEmptySequences.containsAll(other.nonEmptySequences);
    }

    /**
     * Whether a reading opened this way holds of the values this context describes.
     *
     * <p>Exhaustive over {@link RootOpening}, with no {@code default}: a way of opening a reading
     * added later stops this compiling rather than joining whichever side its author's condition
     * happened to leave it on — which, for a reading that is met into a constraint space, is the
     * difference between rules that hold of every row and rules that hold of some.
     *
     * <p>A narrowing this context does not select is not refused here. What such a case says is left
     * out of the space, and whether any value stands under it at all is the other question
     * ({@code emptiness}) — asked of every alternative rather than of the one a caller happened to
     * name.
     */
    boolean holds(RootOpening opening) {
        return switch (opening) {
            case RootOpening.Taken _ -> true;
            case RootOpening.Refined it ->
                    it.crossing().branch().equals(refinements.at(it.crossing().sum()));
            case RootOpening.Inside it -> nonEmptySequences.contains(it.sequence());
        };
    }
}
