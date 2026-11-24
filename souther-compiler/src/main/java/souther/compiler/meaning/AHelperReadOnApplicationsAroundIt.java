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
 * A helper a comparison is written in, a copy of which stands in more than one application of a
 * closure that a call outside that copy makes: the helper an author declares as a behavior so that
 * those applications no longer read the comparison again in each of them.
 *
 * <p>Read off where each copy stands and which call applies a closure around that copy, and
 * nothing else. Which helper wrote the comparison is the innermost helper of its copy
 * ({@link CaseExpansion#writtenInside}), and whether a call is outside that copy is whether the call
 * stands in it. Declared as a behavior, the helper reads the comparison over its own inputs, once,
 * and the applications around its calls hand it a value each. What that leaves for each rule is
 * another compilation, and nothing here says it.
 *
 * <p><b>A copy and the call around it, held together.</b> One helper is called inside several
 * functions, and what one call applies around one copy is nothing about another copy. So the
 * readings this is made of are each a copy with a call around it ({@link ReadAgain}), and every
 * answer is of those pairs: which calls a reading at some copies stands in
 * ({@link #restrictedTo}), and what declaring another helper would take away ({@link
 * #leftReadAgainBy}).
 *
 * <p><b>Beside the helper that holds every choice, and never in place of it.</b> That one
 * ({@link CaseExpansion#theHelperHoldingEveryChoice}) holds the choices and not the comparison,
 * and says nothing where a part's maker is not known. This holds the comparison and none of the
 * applications, so a part nothing was found to have made says nothing about it.
 *
 * <p><b>Not a call made twice.</b> Two calls of a helper on two arms of an {@code if} read it
 * twice, once on each arm, and add to the ways rather than multiply them; and a closure applied
 * once reads what it holds once. Only a call applying a closure more than once around a copy
 * names the helper. Nor a closure written inside the helper: its applications stand in the
 * helper's copy and are read again however the helper is declared.
 *
 * @param helper the helper the comparison is written in
 * @param around each copy of the comparison with a call outside it that applies a closure around
 *               it more than once, in the order they are met
 */
public record AHelperReadOnApplicationsAroundIt(ValueName.Helper helper, List<ReadAgain> around) {

    public AHelperReadOnApplicationsAroundIt {
        Objects.requireNonNull(helper, "some helper the comparison is written in");
        around = List.copyOf(around);
        if (around.isEmpty()) {
            throw new IllegalArgumentException("a helper is read on the applications of some call");
        }
    }

    /**
     * A copy of a comparison, a call that applies a closure the copy stands in, and on how many
     * of that call's applications the copy stands.
     *
     * @param copy         the copy of the comparison
     * @param call         the call, in the copy of the model it stands in
     * @param applications how many of its applications the copy stands on
     */
    public record ReadAgain(ModelOccurrence copy, ModelOccurrence call, int applications) {

        public ReadAgain {
            Objects.requireNonNull(copy, "a copy of some comparison");
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
     * The helper the copies in {@code read} are written in, with each of {@code read} whose call
     * stands outside its copy and applies a closure around it more than once; empty where a copy
     * is written in the behavior's own body, where they are not all one helper's, or where none is.
     */
    public static Optional<AHelperReadOnApplicationsAroundIt> of(Collection<ReadAgain> read) {
        Set<ValueName.Helper> writers = new LinkedHashSet<>();
        for (ReadAgain each : read) {
            Optional<ValueName.Helper> writer = writtenIn(each.copy());
            if (writer.isEmpty()) {
                return Optional.empty();
            }
            writers.add(writer.get());
        }
        if (writers.size() != 1) {
            return Optional.empty();
        }
        ValueName.Helper helper = writers.iterator().next();
        List<ReadAgain> around = new ArrayList<>();
        for (ReadAgain each : read) {
            if (each.applications() > 1
                    && !standsIn(each.call().lineage(), copyOf(each.copy().lineage(), helper))) {
                around.add(each);
            }
        }
        return around.isEmpty() ? Optional.empty()
                : Optional.of(new AHelperReadOnApplicationsAroundIt(helper, around));
    }

    /** The calls around these copies, each once, in the order they are met. */
    public List<ModelOccurrence> calls() {
        Set<ModelOccurrence> out = new LinkedHashSet<>();
        around.forEach(each -> out.add(each.call()));
        return List.copyOf(out);
    }

    /**
     * The same, of the copies a reading was read at alone: the calls around those copies and no
     * other's. Empty where none of them is around any.
     */
    public Optional<AHelperReadOnApplicationsAroundIt> restrictedTo(
            Collection<ModelOccurrence> readAt) {
        List<ReadAgain> kept = around.stream().filter(each -> readAt.contains(each.copy()))
                .toList();
        return kept.isEmpty() ? Optional.empty()
                : Optional.of(new AHelperReadOnApplicationsAroundIt(helper, kept));
    }

    /**
     * Of {@code suggested}, the helpers that, declared as a behavior, leave some copy read again
     * on each application of the call around it. Each once, in the order given, and never this
     * helper.
     *
     * <p>A helper takes a copy out of the applications around it only where the copy stands in a
     * copy of that helper and the call does not: the comparison then is read in the helper's own
     * body, and the applications hand the helper a value each. One the copy does not stand in is
     * expanded somewhere else and leaves the copy where it was; one the call stands in as well
     * takes both into its own body, where the call applies the closure to each element as before.
     * A fact about where the copy and the call stand, and no reckoning of what either suggestion
     * would cost.
     */
    public List<ValueName.Helper> leftReadAgainBy(Collection<ValueName.Helper> suggested) {
        Set<ValueName.Helper> out = new LinkedHashSet<>();
        for (ValueName.Helper each : suggested) {
            if (!each.equals(helper) && around.stream().anyMatch(read -> !takenOut(read, each))) {
                out.add(each);
            }
        }
        return List.copyOf(out);
    }

    /** Whether declaring {@code declared} takes {@code read}'s copy out of the applications of
     *  its call: the copy stands in a copy of it and the call does not. */
    private static boolean takenOut(ReadAgain read, ValueName.Helper declared) {
        ExpansionLineage.Expansion inside = innermostCopyOf(read.copy().lineage(), declared);
        return inside != null && !standsIn(read.call().lineage(), inside);
    }

    /** The innermost copy of {@code helper}'s body {@code lineage} stands in. */
    private static ExpansionLineage.Expansion copyOf(ExpansionLineage lineage,
                                                    ValueName.Helper helper) {
        ExpansionLineage.Expansion out = innermostCopyOf(lineage, helper);
        if (out == null) {
            throw new IllegalArgumentException(lineage + " stands in no copy of " + helper);
        }
        return out;
    }

    /** The innermost copy of {@code helper}'s body {@code lineage} stands in, or null where it
     *  stands in none. */
    private static ExpansionLineage.Expansion innermostCopyOf(ExpansionLineage lineage,
                                                             ValueName.Helper helper) {
        for (ExpansionLineage each = lineage;
                each instanceof ExpansionLineage.Expansion step; each = step.within()) {
            if (step.expanded().equals(helper)) {
                return step;
            }
        }
        return null;
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
