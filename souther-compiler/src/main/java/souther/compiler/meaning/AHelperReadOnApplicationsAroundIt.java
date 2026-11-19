package souther.compiler.meaning;

import souther.compiler.types.ExpansionLineage;
import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;

/**
 * A helper a comparison is written in, whose copies stand in more than one application of a
 * closure that a call outside them makes: the helper an author declares as a behavior so that
 * those applications no longer read the comparison again in each of them.
 *
 * <p>Read off where the copies stand and nothing else. Which helper wrote the comparison is the
 * innermost helper of its copy ({@link CaseExpansion#writtenInside}), and whether a call is
 * outside that copy is whether the call stands in it. Declared as a behavior, the helper reads the
 * comparison over its own inputs, once, and the applications around its calls hand it a value
 * each: nothing of them is around the comparison any more. What that leaves for each rule is
 * another compilation, and nothing here says it.
 *
 * <p><b>Beside the helper that holds every choice, and never in place of it.</b> That one
 * ({@link CaseExpansion#theHelperHoldingEveryChoice}) holds the choices and not the comparison,
 * and says nothing where a part's maker is not known. This holds the comparison and none of the
 * applications, so a part nothing was found to have made says nothing about it: what is asked is
 * where the comparison's copies stand, and that is known of each.
 *
 * <p><b>Not a call made twice.</b> Two calls of a helper on two arms of an {@code if} read it
 * twice, once on each arm, and add to the ways rather than multiply them; and a closure applied
 * once reads what it holds once. Only a call applying a closure more than once around the copies
 * names the helper. Nor a closure written inside the helper: its applications stand in the
 * helper's copy and are read again however the helper is declared.
 *
 * @param helper the helper the comparison is written in
 * @param calls  the calls outside its copies that apply a closure around them more than once, each
 *               once, in the order they are met
 */
public record AHelperReadOnApplicationsAroundIt(ValueName.Helper helper,
                                                List<ModelOccurrence> calls) {

    public AHelperReadOnApplicationsAroundIt {
        Objects.requireNonNull(helper, "some helper the comparison is written in");
        calls = List.copyOf(calls);
        if (calls.isEmpty()) {
            throw new IllegalArgumentException("a helper is read on the applications of some call");
        }
    }

    /**
     * A call that applies a closure, and on how many of its applications what is asked about was
     * read.
     *
     * @param call         the call, in the copy of the model it stands in
     * @param applications how many of its applications
     */
    public record Applied(ModelOccurrence call, int applications) {

        public Applied {
            Objects.requireNonNull(call, "applications are made by some call");
            if (applications < 1) {
                throw new IllegalArgumentException("a closure applied is applied some times: "
                        + applications);
            }
        }
    }

    /**
     * The helper {@code copy} of a comparison is written in, or empty where it is written in the
     * behavior's own body.
     */
    public static Optional<ValueName.Helper> writtenIn(ModelOccurrence copy) {
        List<ValueName.Helper> out = CaseExpansion.writtenInside(copy);
        return out.isEmpty() ? Optional.empty() : Optional.of(out.getFirst());
    }

    /**
     * The helper the comparisons read at {@code copies} are written in, where some call in
     * {@code applied} outside every one of them applies a closure around them more than once;
     * empty where a copy is written in the behavior's own body, where they are not all one
     * helper's, or where no such call is.
     *
     * @param copies  the copies of the comparisons the readings asked about were read at
     * @param applied the calls whose applications those readings were read on, or inside
     */
    public static Optional<AHelperReadOnApplicationsAroundIt> of(
            Collection<ModelOccurrence> copies, Collection<Applied> applied) {
        Set<ValueName.Helper> writers = new LinkedHashSet<>();
        List<ExpansionLineage.Expansion> helperCopies = new ArrayList<>();
        for (ModelOccurrence copy : copies) {
            Optional<ValueName.Helper> writer = writtenIn(copy);
            if (writer.isEmpty()) {
                return Optional.empty();
            }
            writers.add(writer.get());
            helperCopies.add(copyOf(copy.lineage(), writer.get()));
        }
        if (writers.size() != 1) {
            return Optional.empty();
        }
        Set<ModelOccurrence> around = new LinkedHashSet<>();
        for (Applied each : applied) {
            if (each.applications() > 1 && helperCopies.stream()
                    .noneMatch(inside -> standsIn(each.call().lineage(), inside))) {
                around.add(each.call());
            }
        }
        return around.isEmpty() ? Optional.empty()
                : Optional.of(new AHelperReadOnApplicationsAroundIt(writers.iterator().next(),
                        List.copyOf(around)));
    }

    /**
     * Of {@code suggested}, the helpers that, declared as a behavior, leave the comparison read at
     * {@code copies} in the behavior, and so read again on each application of {@link #calls}:
     * those some copy does not stand in a copy of. Each once, in the order given.
     *
     * <p>What tells this suggestion from another made at the same comparison, and a fact about
     * where the copies stand rather than a guess at what either would cost. A helper the copies
     * stand in takes the comparison into its own body, and the applications around its calls hand
     * it a value each; one they do not stand in is expanded somewhere else, and whatever it takes
     * away, these applications still read the comparison.
     */
    public List<ValueName.Helper> leftReadAgainBy(Collection<ValueName.Helper> suggested,
                                                  Collection<ModelOccurrence> copies) {
        Set<ValueName.Helper> out = new LinkedHashSet<>();
        for (ValueName.Helper each : suggested) {
            if (!each.equals(helper) && copies.stream()
                    .anyMatch(copy -> !CaseExpansion.writtenInside(copy).contains(each))) {
                out.add(each);
            }
        }
        return List.copyOf(out);
    }

    /** The innermost copy of {@code helper}'s body {@code lineage} stands in. */
    private static ExpansionLineage.Expansion copyOf(ExpansionLineage lineage,
                                                    ValueName.Helper helper) {
        for (ExpansionLineage each = lineage;
                each instanceof ExpansionLineage.Expansion step; each = step.within()) {
            if (step.expanded().equals(helper)) {
                return step;
            }
        }
        throw new IllegalArgumentException(lineage + " stands in no copy of " + helper);
    }

    /** Whether {@code lineage} is {@code copy} or stands inside it. */
    private static boolean standsIn(ExpansionLineage lineage, ExpansionLineage.Expansion copy) {
        for (ExpansionLineage each = lineage;
                each instanceof ExpansionLineage.Expansion step; each = step.within()) {
            if (step.equals(copy)) {
                return true;
            }
        }
        return false;
    }
}
