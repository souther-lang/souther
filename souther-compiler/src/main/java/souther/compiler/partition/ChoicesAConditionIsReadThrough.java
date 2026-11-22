package souther.compiler.partition;

import souther.compiler.check.AnOperationApplied;
import souther.compiler.check.Choice;
import souther.compiler.check.DeclarationNewtypes;
import souther.compiler.check.ScopeStep;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.inputs.Denotation;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Set;

/**
 * The choices the values a condition is about are made through, as they are written: every
 * {@code if}, {@code match} and attempted construction on the way from the condition to the places
 * its values come from, each once.
 *
 * <p>Read off how the values are written and of nothing any condition states, so it costs a walk
 * of what the condition reaches. What a called behavior answers is one value, whatever its body
 * chooses by, and so is what a recursive helper answers; and the body of a closure is read on what
 * it is applied to, which is told apart from this.
 */
final class ChoicesAConditionIsReadThrough {

    private final Symbols symbols;
    private final DeclarationNewtypes newtypes;
    private final Set<Core> met = Collections.newSetFromMap(new IdentityHashMap<>());
    private final List<AChoiceReadThrough> choices = new ArrayList<>();

    private ChoicesAConditionIsReadThrough(Symbols symbols, DeclarationNewtypes newtypes) {
        this.symbols = symbols;
        this.newtypes = newtypes;
    }

    /** The choices {@code condition}, its names read as {@code reads} has them, is read through. */
    static List<AChoiceReadThrough> of(Core condition, InputReads reads, InputReading read) {
        ChoicesAConditionIsReadThrough walk = new ChoicesAConditionIsReadThrough(
                read.symbols(), read.newtypes());
        walk.below(Core.withoutStanding(condition), reads);
        return List.copyOf(walk.choices);
    }

    private void reach(Core standing, InputReads reads) {
        Core e = Core.withoutStanding(standing);
        if (!met.add(e) || e instanceof Core.Block || answersOneValue(e)) {
            return;
        }
        if (e instanceof Core.Read) {
            for (Denotation given : reads.boundTo(e, symbols, newtypes)) {
                reach(given.value(), given.at());
            }
            return;
        }
        ConstructOccurrence at = occurrenceOf(e);
        Choice choice = at == null ? null : Choice.of(e);
        if (choice != null) {
            int taken = (int) choice.arms().stream().filter(arm ->
                    !(Core.withoutStanding(arm.answers()) instanceof Core.Unreachable)).count();
            ModelOccurrence.statedAt(at).ifPresent(construct ->
                    choices.add(new AChoiceReadThrough(construct, taken)));
        }
        below(e, reads);
    }

    private void below(Core e, InputReads reads) {
        ScopeStep.forEachChild(e, (child, step) ->
                reach(child, reads.entering(step, symbols, newtypes)));
    }

    /** Whether {@code e} is a call the source left standing: of a behavior, or of a helper that
     *  reaches itself. Its answer is a value a run works out, and no choice in its body is read. */
    private static boolean answersOneValue(Core e) {
        return Core.withoutStanding(e) instanceof Core.Call call
                && AnOperationApplied.of(call) instanceof AnOperationApplied made
                && !(made.operation() instanceof ValueName.Stdlib);
    }

    private static ConstructOccurrence occurrenceOf(Core e) {
        return switch (Core.withoutStanding(e)) {
            case Core.If iff -> iff.place().occurrence();
            case Core.Match match -> match.place().occurrence();
            case Core.IfConstructed attempt -> attempt.place().occurrence();
            default -> null;
        };
    }
}
