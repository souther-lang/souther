package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.types.BindingId;
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
 * The containers a closure of a body is applied over, where every application of it is one a
 * library operation makes over one of them.
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
 * that says nothing, and a closure with one is left out.
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
    private final Map<Core.Block, List<Core>> over = new IdentityHashMap<>();
    private final Set<Core.Block> used = Collections.newSetFromMap(new IdentityHashMap<>());

    private ClosureEntries(Map<BindingId, Core> held) {
        this.held = held;
    }

    /**
     * For each parameter of each closure written in {@code roots} whose every use is an operation
     * applying it, the containers those operations walk — one for each operation, any one of which
     * holding something is what enters the closure.
     *
     * @param held what each name of the body was bound to
     */
    static Map<BindingId, List<Core>> of(List<Core> roots, Map<BindingId, Core> held) {
        ClosureEntries entries = new ClosureEntries(held);
        roots.forEach(root -> entries.visit(root, Standing.ELSEWHERE));
        Map<BindingId, List<Core>> out = new LinkedHashMap<>();
        entries.over.forEach((block, containers) -> {
            if (entries.used.contains(block)) {
                return;
            }
            for (Core.Binder param : block.params()) {
                if (param != null && param.binding() != null) {
                    out.put(param.binding(), List.copyOf(containers));
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
        ValueName operation = operationOf(e);
        List<Core> args = argsOf(e);
        if (operation != null) {
            Combinators.Handed handed =
                    Combinators.handedTo(operation, args, closure -> blockOf(closure));
            if (handed != null) {
                List<Core> containers =
                        over.computeIfAbsent(handed.step(), _ -> new ArrayList<>());
                if (containers.stream().noneMatch(each -> each == handed.container())) {
                    containers.add(handed.container());
                }
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

    private static ValueName operationOf(Core e) {
        return switch (Core.withoutStanding(e)) {
            case Core.Call call when call.fn() instanceof Core.Reached reached ->
                    reached.denotes();
            case Core.PreservedCall preserved -> preserved.declared().operation();
            default -> null;
        };
    }

    private static List<Core> argsOf(Core e) {
        return switch (Core.withoutStanding(e)) {
            case Core.Call call -> call.args();
            case Core.PreservedCall preserved -> preserved.args();
            default -> List.of();
        };
    }
}
