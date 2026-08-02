package souther.compiler.check;

import souther.compiler.Prelude;
import souther.compiler.ast.Ast;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Resolves standard-library {@code exposing} imports (spec §stdlib). Souther auto-imports nothing:
 * a module reaches the library either qualified ({@code List.map}) or by importing the names it
 * wants — {@code import List ( map, filter )} — after which it may write them bare. This pass turns
 * each such bare call into its qualified form up front, so the rest of the compiler only ever sees
 * qualified library calls; the {@code import List ( ... )} lines are then dropped from the module.
 *
 * <p>It mirrors Elm's {@code import List exposing (map)}: the qualified access always works, and the
 * import merely lets a name be written without its qualifier. A name exposed from two libraries at
 * once is ambiguous and rejected — qualify it instead.
 */
public final class Exposing {

    private Exposing() {}

    /**
     * The library names {@code module} may write bare, keyed by the bare spelling.
     *
     * <p>An import says which names a module may write without their qualifier. It does not say what
     * any of them means where it is written: a binding in force wins over an import, and only the
     * pass that knows the bindings can say that. So this answers what the imports bring in, and
     * resolution decides what each name means with that in hand.
     */
    public static Map<String, String> exposedNames(Ast.Module module) {
        return validate(module).exposed;
    }

    /** What the imports bring in, and the imports that are not the library's. */
    private record Validated(Map<String, String> exposed, List<Ast.Import> kept) {}

    /**
     * The library names an import brings in, with the two things an import can get wrong reported:
     * a name the library does not have, and one name brought in from two modules at once.
     *
     * <p>A name the module declares itself is not brought in. That is the module's own name, and one
     * declaration wins over an import — the same way a binding in force wins over both, which is
     * decided where the bindings are known.
     */
    private static Validated validate(Ast.Module module) {
        Set<String> ownNames = new HashSet<>();
        for (Ast.FnDef fn : module.fns()) {
            ownNames.add(fn.name());
        }
        for (Ast.BehaviorDef b : module.behaviors()) {
            ownNames.add(b.name());
        }

        Map<String, String> exposed = new HashMap<>();
        List<Ast.Import> kept = new ArrayList<>();
        for (Ast.Import imp : module.imports()) {
            if (!Prelude.isQualifier(imp.module())) {
                kept.add(imp);   // an ordinary user-module import — resolved elsewhere
                continue;
            }
            for (String name : imp.names()) {
                String qualified = imp.module() + "." + name;
                if (!Prelude.hasQualified(qualified)) {
                    throw CompileException.of(
                            Diagnostic.of(null, "check.import.notstdfn").title("check.module.title")
                                    .at(imp.pos()).args(name, imp.module()).build(),
                            "`" + name + "` is not a function in the standard library module `"
                                    + imp.module() + "` (spec §stdlib).");
                }
                if (ownNames.contains(name)) {
                    continue;   // the module defines its own `name`; that shadows the import
                }
                String prior = exposed.putIfAbsent(name, qualified);
                if (prior != null && !prior.equals(qualified)) {
                    throw CompileException.of(
                            Diagnostic.of(null, "check.import.ambiguous").title("check.module.title")
                                    .at(imp.pos()).args(name, prior, qualified).build(),
                            "`" + name + "` is exposed from both `" + prior + "` and `" + qualified
                                    + "` — call it qualified instead of importing both (spec §stdlib).");
                }
            }
        }
        return new Validated(exposed, kept);
    }

    /**
     * {@code module} with its {@code import List ( ... )} lines dropped, having checked them.
     *
     * <p>What they brought in is answered by {@link #exposedNames} and settled where the bindings
     * are known. Nothing in the module is rewritten here: a name written bare is still written bare,
     * and what it means is one question asked in one place.
     */
    public static Ast.Module withoutLibraryImports(Ast.Module module) {
        List<Ast.Import> kept = validate(module).kept;
        if (kept.size() == module.imports().size()) {
            return module;
        }
        return new Ast.Module(module.name(), module.exposing(), module.exposedOutputs(),
                kept, module.defs(), module.behaviors(), module.fns(),
                module.examples(), module.fakes(), module.exampleFileTarget(), module.pos());
    }

}
