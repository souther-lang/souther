package souther.compiler.inputs;

import souther.compiler.collect.InTheOrderGiven;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * What a question about an input assumes stands: the narrowings it selects, and the containers it
 * needs to hold an element.
 *
 * <p>Every position of an input exists under conditions. A field of a case is there where the value
 * turned out to be that case; a field of an element is there where the container holds one. So a
 * question naming positions is a question asked of the rows that meet those conditions, and which
 * rules reach it is settled by that and by nothing else ({@link #holds}).
 *
 * <p>And a container may be asked of holding none: what a walk over its elements comes to is a
 * number of the container of none as well, so a question about one where nothing says whether the
 * container holds something is asked of it holding something and of it holding none, as a sum is
 * asked of each of its cases ({@link #holdingNothing}).
 *
 * <p><b>Structural and nothing else.</b> It records the refinements selected and the containers
 * required to hold an element or none. It holds no numeric constraint, no fixed value and no
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
record StructuralContext(Requirements refinements, Set<TermPath> nonEmptyContainers,
                         Set<TermPath> emptyContainers) {

    /** A question that assumes nothing: the parameters, and whatever stands under no condition. */
    static final StructuralContext NONE =
            new StructuralContext(Requirements.NONE, Set.of(), Set.of());

    /**
     * One thing a question assumes about the row it is asked of.
     *
     * <p><b>Written down as a kind so that every reading of a context is over all of them.</b> A
     * context is read twice — for which readings of declarations stand in it, and for what it says
     * about the values themselves — and the two are asked in different places by different callers.
     * Held as fields to be remembered one at a time, a kind of prerequisite is read by whichever of
     * them its author happened to touch: which is how the containers came to decide whose rules were
     * read without ever saying that they hold something.
     */
    sealed interface Assumption {

        /** The value at {@code at} turned out to be one of these cases. */
        record TheCaseAt(TermPath at, CasesLeft is) implements Assumption {}

        /** The container at {@code container} holds an element, or the position named inside it
         *  stands nowhere. */
        record HoldingSomething(TermPath container) implements Assumption {}

        /** The container at {@code container} holds no element: how many it holds is none, and
         *  what a walk over its elements comes to is what the walk starts from. */
        record HoldingNothing(TermPath container) implements Assumption {}
    }

    /**
     * Everything this context assumes, in a settled order.
     *
     * <p>The narrowings in the order they were reached and the containers in the order they were
     * needed, which is the order a reason about them reads in. What a reader does with each of them
     * is its own; that it has to answer for every kind of them is this.
     */
    List<Assumption> assumptions() {
        List<Assumption> out = new ArrayList<>();
        refinements.refinements().forEach((at, is) -> out.add(new Assumption.TheCaseAt(at, is)));
        nonEmptyContainers.forEach(each -> out.add(new Assumption.HoldingSomething(each)));
        emptyContainers.forEach(each -> out.add(new Assumption.HoldingNothing(each)));
        return List.copyOf(out);
    }

    /**
     * The containers held as a copy that says its hash without walking it, since a context is
     * what every table of readings under one is keyed by.
     *
     * <p>No container both: a context saying one holds something and holds none describes no row,
     * and none is made — a container is asked of holding none only where nothing has said it holds
     * something ({@link #holdingNothing}).
     */
    StructuralContext {
        nonEmptyContainers = InTheOrderGiven.set(nonEmptyContainers);
        emptyContainers = InTheOrderGiven.set(emptyContainers);
        for (TermPath each : emptyContainers) {
            if (nonEmptyContainers.contains(each)) {
                throw new IllegalArgumentException("`" + each + "` is said to hold something and"
                        + " to hold none");
            }
        }
    }

    /**
     * What naming {@code path} assumes.
     *
     * <p>Both halves read off the path, which is where they are already kept:
     * {@link TermPath#requirements} says which narrowings were taken to get here, and
     * {@link TermPath#containersHoldingIt} says which containers have to hold something for this
     * to be anywhere. Kept beside a path instead, a position would carry a second account of what it
     * already says.
     */
    static StructuralContext of(TermPath path) {
        return new StructuralContext(path.requirements(),
                new LinkedHashSet<>(path.containersHoldingIt()), Set.of());
    }

    /**
     * Both, or the position they disagree about.
     *
     * <p>Refinements are compared by {@link Requirements#merge} and by nothing written here: whether
     * two narrowings hold of one value is that type's question, asked by everything that decides
     * whether two positions can be in one row. Containers only accumulate — needing one to hold an
     * element and needing another to hold one are never at odds. A container held to none is
     * asked of under a context nothing is merged into ({@link #holdingNothing}).
     */
    Merge merge(StructuralContext other) {
        return switch (refinements.merge(other.refinements)) {
            case Requirements.Merge.Conflict it -> new Merge.Disagreeing(it);
            case Requirements.Merge.Merged it -> {
                Set<TermPath> both = new LinkedHashSet<>(nonEmptyContainers);
                both.addAll(other.nonEmptyContainers);
                Set<TermPath> none = new LinkedHashSet<>(emptyContainers);
                none.addAll(other.emptyContainers);
                yield new Merge.Together(new StructuralContext(it.requirements(), both, none));
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
        return new StructuralContext(refinements.and(at, branch), nonEmptyContainers,
                emptyContainers);
    }

    /**
     * The same, with {@code container} required to hold an element as well.
     *
     * <p>What a reader asking whether anything can stand inside a container assumes while it asks.
     * A container that may be empty is a value whatever is true of what it would hold, so the
     * question is only ever asked under this.
     */
    StructuralContext holding(TermPath container) {
        Set<TermPath> more = new LinkedHashSet<>(nonEmptyContainers);
        more.add(container);
        return new StructuralContext(refinements, more, emptyContainers);
    }

    /**
     * The same, with {@code container} holding no element.
     *
     * <p>What a question about a walk over a container's elements is asked of beside the container
     * holding something, where nothing here says which: a sum of them is nought over none, and a
     * question asked of the container holding something alone leaves out every row where it holds
     * none. Never asked where this already says it holds something.
     */
    StructuralContext holdingNothing(TermPath container) {
        Set<TermPath> more = new LinkedHashSet<>(emptyContainers);
        more.add(container);
        return new StructuralContext(refinements, nonEmptyContainers, more);
    }

    /** Whether this says whether {@code container} holds something, one way or the other. */
    boolean says(TermPath container) {
        return nonEmptyContainers.contains(container) || emptyContainers.contains(container);
    }

    /**
     * Whether everything {@code other} assumes is already assumed here.
     *
     * <p>What says a position exists in the values this describes: a sum inside a case is a place to
     * ask about only once the value is that case, and asking about it under a context that has not
     * settled the case would be walking alternatives of a sum that stands nowhere.
     *
     * <p>A case assumed is covered by the same case or by fewer: a context that settled
     * {@code Station} has settled that the value is {@code Station} or {@code Hospital}.
     */
    boolean covers(StructuralContext other) {
        for (Map.Entry<TermPath, CasesLeft> each : other.refinements.refinements().entrySet()) {
            CasesLeft assumed = refinements.at(each.getKey());
            if (assumed == null || !assumed.within(each.getValue())) {
                return false;
            }
        }
        return nonEmptyContainers.containsAll(other.nonEmptyContainers)
                && emptyContainers.containsAll(other.emptyContainers);
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
            // Asked of what is kept rather than of every assumption made anew: a reading asks this
            // for each root it stands under, and one sum has one case taken in at most.
            case RootOpening.Refined it -> CasesLeft.of(it.crossing().branch())
                    .equals(refinements.refinements().get(it.crossing().sum()));
            case RootOpening.Inside it -> nonEmptyContainers.contains(it.container());
        };
    }
}
