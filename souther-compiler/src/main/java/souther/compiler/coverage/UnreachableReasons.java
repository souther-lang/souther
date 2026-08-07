package souther.compiler.coverage;

import souther.compiler.core.Core;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * Why an expression answers nothing, in the words the model wrote.
 *
 * <p>Asked apart from {@link NormalReturn}, which answers whether and not why. An arm made of a
 * {@code match} whose arms each abort for a different reason has no one reason, and taking the first
 * would name whichever the author happened to write above the other. What comes back is every reason
 * on the paths that abort, so the caller can say the single one where there is one and say that there
 * are several where there are.
 */
public final class UnreachableReasons {

    /** Every reason reached along the paths that answer nothing, in the order they are written and
     * without repeats. Empty where the expression answers a value. */
    public static List<String> of(Core e) {
        Set<String> found = new LinkedHashSet<>();
        collect(e, found);
        return List.copyOf(found);
    }

    private static void collect(Core e, Set<String> into) {
        if (NormalReturn.of(e)) {
            return;
        }
        switch (e) {
            case Core.Unreachable u -> into.add(u.reason());
            case Core.Block b -> collect(b.body(), into);
            case Core.LetIn li -> collect(NormalReturn.of(li.value()) ? li.body() : li.value(), into);
            case Core.If iff -> {
                if (!NormalReturn.of(iff.cond())) {
                    collect(iff.cond(), into);
                } else {
                    collect(iff.then(), into);
                    collect(iff.els(), into);
                }
            }
            case Core.Match m -> {
                if (!NormalReturn.of(m.scrutinee())) {
                    collect(m.scrutinee(), into);
                } else {
                    m.cases().forEach(arm -> collect(arm.body(), into));
                }
            }
            case Core.IfConstructed ic -> {
                List<Core> built = ic.construct().inits().stream()
                        .map(Core.FieldInit::value).toList();
                if (built.stream().anyMatch(v -> !NormalReturn.of(v))) {
                    built.forEach(v -> collect(v, into));
                } else {
                    collect(ic.then(), into);
                    ic.els().forEach(arm -> collect(arm.body(), into));
                }
            }
            // Anything else answers nothing because something it evaluates first does.
            default -> children(e).forEach(child -> collect(child, into));
        }
    }

    private static List<Core> children(Core e) {
        List<Core> out = new ArrayList<>();
        Core.forEachChild(e, out::add);
        return out;
    }

    private UnreachableReasons() {}
}
