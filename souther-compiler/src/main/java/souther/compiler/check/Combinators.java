package souther.compiler.check;

import souther.compiler.Prelude;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Which library operations hand a closure the contents of a container, and where: the closure is
 * argument {@code closureArg}, the value it receives is closure parameter {@code elementParam}, and
 * the container it comes from is argument {@code containerArg}.
 *
 * <p>Two checks read this and neither states it. The totality check credits a value a closure is
 * handed as a sub-term of the container, so recursing on it is structural; the invariant-discharge
 * check binds that value to the container's element type, so a construction inside the closure is
 * analyzed rather than left opaque. What each does with the answer is its own; what it asks is one
 * question about the operation.
 *
 * <p>Nothing here is written down. The library's own signature already says which argument takes a
 * function and which parameter of that function has the type of what a container holds, so the rules
 * are read off {@link Prelude}: an operation the library gains is answered for by being declared. A
 * signature this cannot read off — two function arguments, or two closure parameters that could each
 * be the element — raises rather than answering half, because a combinator nobody registered is a
 * check that quietly stops crediting an element.
 *
 * <p>Each reader asks under the name it holds. The totality check reads the tree an author wrote,
 * where {@code List.fold} still spells itself; the discharge check reads one where the rewrite to
 * {@code List.foldFrom} has happened. So a {@linkplain Prelude#rewrites() sugared} name is answered
 * with what it rewrites to, over the arguments the rewrite keeps in place — and the discharge side
 * never asks, because {@link Preserved} is built from declarations and a sugar has none.
 */
final class Combinators {

    /** A combinator's closure, the parameter its element arrives on, and the container it comes
     * from — all as argument positions of the call. */
    record Combinator(int closureArg, int elementParam, int containerArg) {}

    /** What {@code operation} hands its closure, or null where it hands one nothing a container
     * holds — including where it applies no closure at all, and where the name applied is not a
     * library operation. */
    static Combinator of(ValueName operation) {
        return operation == null ? null : Derived.RULES.get(operation);
    }

    /** The operations there is a rule for, for the tests that hold them to firing. */
    static Set<String> names() {
        Set<String> names = new LinkedHashSet<>();
        Derived.RULES.keySet().forEach(operation -> names.add(operation.name()));
        return names;
    }

    /** Read off the library on the first ask. The library is the same library for every module
     * compiled, and reading it is answering the question for all of them at once. */
    private static final class Derived {
        private static final Map<ValueName, Combinator> RULES = read();
    }

    private static Map<ValueName, Combinator> read() {
        Map<ValueName, Combinator> rules = new LinkedHashMap<>();
        Prelude.entries().forEach((qualified, entry) -> {
            Combinator rule = ruleFor(qualified, entry.signature().params());
            if (rule != null) {
                rules.put(new ValueName.Stdlib(qualified), rule);
            }
        });
        Prelude.rewrites().forEach((sugar, rewrite) -> {
            Combinator target = rules.get(new ValueName.Stdlib(rewrite.target()));
            if (target == null) {
                return;   // what it becomes hands its closure nothing, so neither does it
            }
            if (target.closureArg() >= rewrite.keptArgs() || target.containerArg() >= rewrite.keptArgs()) {
                throw new IllegalStateException(sugar + " is sugar for " + rewrite.target()
                        + ", whose closure or container is not among the arguments the rewrite keeps"
                        + " in place — what it hands its closure cannot be said of the sugar");
            }
            rules.put(new ValueName.Stdlib(sugar), target);
        });
        return Collections.unmodifiableMap(rules);
    }

    /**
     * The rule the signature of {@code qualified} states, or null where it states none.
     *
     * <p>The closure is the argument that takes a function. The container is an argument holding
     * something whose element type is the type of one of that closure's parameters — which is what
     * "hands its closure the contents of" means, said in types. An operation whose signature admits
     * more than one reading of either is one this cannot answer for.
     */
    private static Combinator ruleFor(String qualified, List<Type> params) {
        int closureArg = -1;
        for (int i = 0; i < params.size(); i++) {
            if (params.get(i) instanceof Type.FnOf) {
                if (closureArg >= 0) {
                    throw new IllegalStateException(qualified + " takes two functions, so which one is"
                            + " handed the container's elements is not read off its signature");
                }
                closureArg = i;
            }
        }
        if (closureArg < 0) {
            return null;
        }
        List<Type> closureParams = ((Type.FnOf) params.get(closureArg)).params();
        Combinator found = null;
        for (int c = 0; c < params.size(); c++) {
            if (c == closureArg) {
                continue;   // the closure is what receives; it is not what is received from
            }
            Type element = Terms.elementType(params.get(c));
            if (element == null) {
                continue;
            }
            for (int p = 0; p < closureParams.size(); p++) {
                if (!element.equals(closureParams.get(p))) {
                    continue;
                }
                if (found != null) {
                    throw new IllegalStateException(qualified + " could be handing its closure the"
                            + " contents of more than one of its arguments, or on more than one"
                            + " parameter, so which is not read off its signature");
                }
                found = new Combinator(closureArg, p, c);
            }
        }
        return found;
    }

    private Combinators() {}
}
