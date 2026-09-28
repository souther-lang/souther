package souther.compiler.inputs;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

/**
 * The names a narrowing carries across, and the one correspondence between what the value above
 * calls a position and where that position stands.
 *
 * <p>The one way a rule of one value reaches a position of another, and it exists because the
 * language has one: a field every case of a sum spreads is readable on a value of the sum, so a
 * clause written up there is about the field a row writes down here. Nothing else crosses — what a
 * case declares of its own is not readable above it, and a clause of the sum has no name for it.
 *
 * <p><b>Both directions, from one place.</b> A reading of a position asks what the value above
 * calls it; a reading that says the rules of the value above in the words of the case asks where a
 * name of the value above stands. They are one fact, and two owners of it would be free to
 * disagree about which positions a clause reaches.
 *
 * <p><b>Names may be empty, and that is a narrowing nothing crosses.</b> Whether a root stands
 * under a narrowing and whether a name crosses it are two questions ({@link RootOpening.Refined}),
 * and a sum whose cases share nothing is the model where they come apart.
 *
 * @param sum   where the sum stands, which is where the narrowing was taken
 * @param branch which case the value turned out to be
 * @param names the names the cases share, which are the only ones that cross
 */
record SharedNames(TermPath sum, Refinement branch, Set<String> names) {

    SharedNames {
        names = Set.copyOf(names);
    }

    /**
     * What the value above calls the position at {@code here}, or null where it calls it nothing.
     *
     * <p>The narrowing taken back out, which is what a name written above means down here: a row at
     * {@code h.q@A.limit} writes the {@code limit} a clause of {@code h} called {@code q.limit}, and
     * the two differ by the step that says which case the value turned out to be. Null for the case
     * itself and for anything under a name the cases do not share, which is every position the value
     * above cannot name.
     */
    TermPath outerPathOf(TermPath here) {
        List<TermPath.Step> steps = here.steps();
        int narrowing = sum.steps().size();
        if (steps.size() <= narrowing + 1
                || !here.isAtOrUnder(sum)
                || !(steps.get(narrowing) instanceof TermPath.Step.Refine taken)
                || !taken.refinement().equals(branch)
                || !(steps.get(narrowing + 1) instanceof TermPath.Step.Field field)
                || !names.contains(field.name())) {
            return null;
        }
        List<TermPath.Step> without = new ArrayList<>(steps.subList(0, narrowing));
        without.addAll(steps.subList(narrowing + 1, steps.size()));
        return new TermPath(here.head(), without);
    }

    /**
     * Where the position the value above calls {@code there} stands once the value is this case, or
     * null where the name does not cross.
     *
     * <p>{@link #outerPathOf} the other way round. What is put back is the step that says which case
     * the value turned out to be, and everything under the shared name comes with it: a clause
     * relating {@code q.lo} and {@code q.hi} is a clause about the two numbers standing at
     * {@code q@A.lo} and {@code q@A.hi} once the value is an {@code A}.
     */
    TermPath standingUnderTheCase(TermPath there) {
        return under(there, sum, branch, names);
    }

    /**
     * {@link #standingUnderTheCase} with the crossing given as its parts, for a reader holding one
     * name rather than the set a declaration spreads.
     *
     * <p>Here and not written out twice. What the walk observed of a name and what a declaration
     * spreads are two facts about one crossing, and a second copy of the step that says which case
     * the value turned out to be would put a name under a case by one rule here and another one
     * there.
     */
    static TermPath under(TermPath there, TermPath sum, Refinement branch, Set<String> names) {
        String named = nameUnder(there, sum);
        return named != null && names.contains(named) ? withTheCaseTakenIn(there, sum, branch)
                : null;
    }

    /**
     * The same for a reader holding one name rather than the set a declaration spreads.
     *
     * <p>Beside the one above so that such a reader does not gather its name into a set to ask.
     * Both are the same two steps — which name is written under the sum, and the path with the case
     * put in — and each of those is written once.
     */
    static TermPath under(TermPath there, TermPath sum, Refinement branch, String name) {
        return name.equals(nameUnder(there, sum)) ? withTheCaseTakenIn(there, sum, branch) : null;
    }

    /** The name {@code there} is written under at {@code sum}, or null where it is under none. */
    private static String nameUnder(TermPath there, TermPath sum) {
        List<TermPath.Step> steps = there.steps();
        int narrowing = sum.steps().size();
        return steps.size() > narrowing
                && there.isAtOrUnder(sum)
                && steps.get(narrowing) instanceof TermPath.Step.Field field
                ? field.name() : null;
    }

    /** {@code there} with the step that says which case the value turned out to be put in. */
    private static TermPath withTheCaseTakenIn(TermPath there, TermPath sum, Refinement branch) {
        List<TermPath.Step> steps = there.steps();
        int narrowing = sum.steps().size();
        List<TermPath.Step> under = new ArrayList<>(steps.subList(0, narrowing));
        under.add(new TermPath.Step.Refine(branch));
        under.addAll(steps.subList(narrowing, steps.size()));
        return new TermPath(there.head(), under);
    }
}
