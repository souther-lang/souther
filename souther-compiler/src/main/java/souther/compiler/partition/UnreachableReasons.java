package souther.compiler.partition;

import souther.compiler.ast.Hir;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeOps;
import souther.compiler.core.Core;
import souther.compiler.coverage.NormalReturn;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Why an expression answers nothing, in the words the model wrote.
 *
 * <p>Asked apart from {@link NormalReturn}, which answers whether and not why. An arm made of a
 * {@code match} whose arms each abort for a different reason has no one reason, and taking the first
 * would name whichever the author happened to write above the other. What comes back is every reason
 * on the paths that abort, so the caller can say the single one where there is one and say that there
 * are several where there are.
 *
 * <p>Every reason on those paths, and nothing after evaluation stops. A construction whose first
 * field aborts never evaluates the second, so a second {@code unreachable} written below it is not a
 * reason this value did not arrive — it is text that never runs. Paths that a fork keeps apart are
 * all read, because each of them is a way this expression fails to answer.
 *
 * <p>Which of them is first is the order the values are <em>evaluated</em> in, and for a construction
 * that is the order the fields are declared rather than the order the initializers are written: the
 * emitter walks the declared fields and picks each one's initializer out. {@code Core.forEachChild}
 * hands over the slots of a node and is not an account of evaluation, so nothing here takes it for
 * one where the two can differ.
 */
public final class UnreachableReasons {

    /** Every reason reached along the paths that answer nothing, in the order they are evaluated and
     * without repeats. Empty where the expression answers a value. */
    public static List<String> of(Core e, Symbols symbols) {
        Set<String> found = new LinkedHashSet<>();
        collect(e, symbols, found);
        return List.copyOf(found);
    }

    private static void collect(Core e, Symbols symbols, Set<String> into) {
        if (NormalReturn.of(e)) {
            return;
        }
        switch (e) {
            case Core.Unreachable u -> into.add(u.reason());
            case Core.LetIn li -> collect(
                    NormalReturn.of(li.value()) ? li.body() : li.value(), symbols, into);
            case Core.If iff -> {
                if (!NormalReturn.of(iff.cond())) {
                    collect(iff.cond(), symbols, into);
                } else {
                    collect(iff.then(), symbols, into);
                    collect(iff.els(), symbols, into);
                }
            }
            case Core.Match m -> {
                if (!NormalReturn.of(m.scrutinee())) {
                    collect(m.scrutinee(), symbols, into);
                } else {
                    m.cases().forEach(arm -> collect(arm.body(), symbols, into));
                }
            }
            case Core.NewData nd -> {
                Core stops = evaluated(nd, symbols);
                if (stops != null) {
                    collect(stops, symbols, into);
                }
            }
            case Core.IfConstructed ic -> {
                Core stops = evaluated(ic.construct(), symbols);
                if (stops != null) {
                    collect(stops, symbols, into);
                } else {
                    collect(ic.then(), symbols, into);
                    ic.els().forEach(arm -> collect(arm.body(), symbols, into));
                }
            }
            // Anything else answers nothing because something it evaluates first does, and the rest
            // of what is written in it never runs.
            default -> {
                Core stops = firstThatAborts(children(e));
                if (stops != null) {
                    collect(stops, symbols, into);
                }
            }
        }
    }

    /**
     * The initializer a construction stops at, or null where every one of them answers.
     *
     * <p>Read in declaration order, which is the order the fields are pushed. Written order would
     * name whichever {@code unreachable} the author put uppermost, and a construction that names its
     * fields in another order than the data declares them is ordinary.
     */
    private static Core evaluated(Core.NewData nd, Symbols symbols) {
        Map<String, Core> byName = new LinkedHashMap<>();
        nd.inits().forEach(init -> byName.put(init.name(), init.value()));
        List<Core> inOrder = new ArrayList<>();
        for (String field : declaredFields(nd, symbols)) {
            Core value = byName.remove(field);
            if (value != null) {
                inOrder.add(value);
            }
        }
        inOrder.addAll(byName.values());   // a field the declaration does not have, if one ever is
        return firstThatAborts(inOrder);
    }

    /** The fields as the data declares them, or nothing where this construction's type cannot be
     * read — in which case the initializers keep the order they were written in. */
    private static List<String> declaredFields(Core.NewData nd, Symbols symbols) {
        if (symbols == null || !(symbols.declarations().declaration(nd.typeName()) instanceof Hir.Data data)) {
            return List.of();
        }
        Map<String, Type> fields = TypeOps.fieldTypes(data, symbols);
        return List.copyOf(fields.keySet());
    }

    /** The first of a run of strict positions that does not answer, which is where evaluation stops
     * and where every reason below it stops being one. */
    private static Core firstThatAborts(List<Core> evaluated) {
        for (Core each : evaluated) {
            if (!NormalReturn.of(each)) {
                return each;
            }
        }
        return null;
    }

    /** The slots of a node, which for everything reaching here is a run of strict positions in the
     * order they are evaluated. */
    private static List<Core> children(Core e) {
        List<Core> out = new ArrayList<>();
        Core.forEachChild(e, out::add);
        return out;
    }

    private UnreachableReasons() {}
}
