package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.types.BindingId;
import souther.compiler.types.OccurrenceLineage;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Every use of each closure of a body ({@link ClosureUses}): the applications library operations
 * make of it over their containers, and whether anything else uses it.
 *
 * <p>A closure is entered only by an application, and a library operation applies the closure it is
 * handed only where the container it walks holds something. So where the operations are the only
 * ones that apply a closure, it is entered only where one of their containers holds something. That
 * is a fact about the closure as a whole: a closure that is also applied directly, handed to a
 * function of the author's, or kept in a value is applied by something that needs no container, and
 * what one operation over one container says of it is not what a run needs to be inside it.
 *
 * <p>So each use of a closure is accounted for before any is believed. A use is an operation
 * applying it ({@link Combinators#handedTo}), the name or the block it was given standing as the
 * argument that takes the closure; every other place the block or a name bound to it is met is a use
 * that says nothing, and a closure with one enters over no container
 * ({@link ClosureUses#enteredOver}).
 */
final class ClosureEntries {

    /** Where a node stands among the uses of a closure. */
    private enum Standing {
        /** Anywhere a closure is used some way this says nothing of. */
        ELSEWHERE,
        /** The argument an operation takes its closure as. */
        THE_CLOSURE_OF_AN_OPERATION,
        /** The value a name is given, which is where the closure is made and not used. */
        WHERE_IT_IS_NAMED
    }

    private final Map<BindingId, Core> held;
    private final Map<Core.Block, List<ClosureUses.Application>> over = new IdentityHashMap<>();
    private final Set<Core.Block> used = Collections.newSetFromMap(new IdentityHashMap<>());

    private ClosureEntries(Map<BindingId, Core> held) {
        this.held = held;
    }

    /**
     * For each parameter of each closure written in {@code roots} that some operation applies,
     * every use of the closure: each application an operation makes of it, and whether anything
     * else uses it too. A closure no operation applies is not here.
     *
     * @param held what each name of the body was bound to
     */
    static Map<BindingId, ClosureUses> of(List<Core> roots, Map<BindingId, Core> held) {
        ClosureEntries entries = new ClosureEntries(held);
        roots.forEach(root -> entries.visit(root, Standing.ELSEWHERE));
        Map<BindingId, ClosureUses> out = new LinkedHashMap<>();
        entries.over.forEach((block, applications) -> {
            ClosureUses uses = new ClosureUses(applications, entries.used.contains(block));
            for (Core.Binder param : block.params()) {
                if (param != null && param.binding() != null) {
                    out.put(param.binding(), uses);
                }
            }
        });
        return out;
    }

    private void visit(Core e, Standing standing) {
        Core.Block block = blockOf(e);
        if (block != null && standing == Standing.ELSEWHERE) {
            used.add(block);
        }
        Called called = calledAt(e);
        if (called != null) {
            Combinators.Handed handed = Combinators.handedTo(called.operation(), called.args(),
                    closure -> blockOf(closure));
            if (handed != null) {
                over.computeIfAbsent(handed.step(), _ -> new ArrayList<>())
                        .add(new ClosureUses.Application(called.operation(), called.lineage(),
                                handed.container(), handed.applied(), e,
                                handed.position() == null ? null
                                        : handed.position().binding()));
                Core.forEachChild(e, child -> visit(child,
                        Core.withoutStanding(child) == Core.withoutStanding(handed.closure())
                                ? Standing.THE_CLOSURE_OF_AN_OPERATION : Standing.ELSEWHERE));
                return;
            }
        }
        switch (e) {
            case Core.LetIn let -> {
                visit(let.value(), blockOf(let.value()) != null ? Standing.WHERE_IT_IS_NAMED
                        : Standing.ELSEWHERE);
                visit(let.body(), Standing.ELSEWHERE);
            }
            // Standing as a wider type changes nothing about which use the value is.
            case Core.Widen _ -> Core.forEachChild(e, child -> visit(child, standing));
            default -> Core.forEachChild(e, child -> visit(child, Standing.ELSEWHERE));
        }
    }

    /**
     * The block {@code e} is, or that the name it reads was given, through any number of names;
     * null where it is neither.
     */
    private Core.Block blockOf(Core e) {
        Set<BindingId> met = new HashSet<>();
        Core at = Core.withoutStanding(e);
        while (at instanceof Core.Read read) {
            if (read.binding() == null || !met.add(read.binding())) {
                return null;
            }
            Core given = held.get(read.binding());
            at = given == null ? null : Core.withoutStanding(given);
        }
        return at instanceof Core.Block block ? block : null;
    }

    /**
     * A call of something a name reached: what it applies, which copy of a body it stands in, and
     * what it is handed.
     */
    private record Called(ValueName operation, OccurrenceLineage lineage, List<Core> args) {}

    /** The call {@code e} is, or null where it is no call of something a name reached. */
    private static Called calledAt(Core e) {
        return switch (Core.withoutStanding(e)) {
            case Core.Call call when call.fn() instanceof Core.Reached reached ->
                    new Called(reached.denotes(), call.occurrence().lineage(), call.args());
            case Core.PreservedCall preserved -> new Called(preserved.declared().operation(),
                    preserved.place().lineage(), preserved.args());
            default -> null;
        };
    }
}
