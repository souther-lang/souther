package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.types.Type;

import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * What each call standing in one body decides for the variables its callee's signature left open.
 *
 * <p>A library signature is resolved once, when the library is loaded, and every call site reads that
 * one value; nothing instantiates it. A call builds its own bindings and substitutes, so a variable
 * the call solves becomes what it was solved to and one it does not solve comes back out as the
 * variable the library wrote. Two unrelated calls therefore hand back one name — {@code List.length}
 * and {@code Set.size} both wrote {@code 'a} — and a parameter that took its answer from each of them
 * would claim the two hold the same thing.
 *
 * <p>So the instantiation that never happened is done here, and it belongs to <em>the call</em>. One
 * application of a signature decides its variables once, and every parameter of the helper that reads
 * that call reads the same decision: {@code Set.contains(v, s)} says {@code v} is what {@code s}
 * holds, whichever of the two the walk is settling. Deciding afresh for each parameter would say that
 * of neither.
 *
 * <p>An expansion follows the same rule where it inlines a call, instantiating the callee's signature
 * once over the bindings its arguments become. Whether a call stands or is expanded is then not
 * something the answer depends on.
 */
final class Freshening {

    /** What each call has decided, by the call it is. Two calls written the same way are two
     * applications, so they are told apart by which node they are and not by how they read. */
    private final Map<Ast.Apply, Map<String, Type>> decided = new IdentityHashMap<>();

    /**
     * What {@code call} decides for the variables {@code declared} left open — one fresh variable
     * each, and the same ones every time this call is asked. Empty where the declaration left none
     * open, which is most calls.
     */
    Map<String, Type> of(Ast.Apply call, List<Type> declared) {
        Map<String, Type> already = decided.get(call);
        if (already != null) {
            return already;
        }
        Map<String, Type> theirs = new LinkedHashMap<>();
        String at = "c" + decided.size();
        for (Type t : declared) {
            collect(t, at, theirs);
        }
        decided.put(call, theirs);
        return theirs;
    }

    private static void collect(Type t, String at, Map<String, Type> theirs) {
        if (t == null) {
            return;
        }
        Type.mentions(t, x -> {
            if (x instanceof Type.Var v && !theirs.containsKey(v.name())) {
                theirs.put(v.name(), Type.inferredVar(v.name() + "." + at));
            }
            return false;   // a collector, not a test: every position is visited
        });
    }
}
