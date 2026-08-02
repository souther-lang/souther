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
 * Reads standard-library {@code exposing} imports (spec §stdlib). Souther auto-imports nothing: a
 * module reaches the library either qualified ({@code List.map}) or by importing the names it wants
 * — {@code import List ( map, filter )} — after which it may write them bare.
 *
 * <p>What the imports bring in is answered as a table ({@link #read}) and nothing in the
 * module is rewritten. A name written bare stays written bare, and what it means where it is written
 * is settled once, by resolution, with the bindings in force — an import is the last thing consulted
 * and a binding or the module's own declaration wins over it. The {@code import List ( ... )} lines
 * are then dropped ({@link #withoutLibraryImports}), having been checked.
 *
 * <p>It mirrors Elm's {@code import List exposing (map)}: the qualified access always works, and the
 * import merely lets a name be written without its qualifier. A name exposed from two libraries at
 * once is ambiguous and rejected — qualify it instead.
 */
public final class Exposing {

    private Exposing() {}

    /**
     * What the imports bring in, the imports that are not the library's, and the import lines that
     * name something this module already declares.
     *
     * <p>A collision is answered rather than thrown because it is one module's mistake and not a
     * reason to stop reading. Thrown, it escaped the question that asked for this module and took
     * every other file's diagnostics with it — an editor showed "the compiler could not finish
     * reading this file" for the whole workspace while the author was part-way through writing a
     * {@code let}.
     */
    public record Validated(Map<String, String> exposed, List<Ast.Import> kept,
                            List<Diagnostic> conflicts) {}

    /** Both answers at once, for a reader that wants them both and should ask once. */
    public static Validated read(Ast.Module module) {
        return validate(module);
    }

    /**
     * The library names an import brings in, with the three things an import can get wrong reported:
     * a name the library does not have, one name brought in from two modules at once, and one that
     * collides with something this module declares.
     *
     * <p>Which kind of declaration it collides with does not enter into it. A data, a {@code let}
     * and a behavior all reach the value namespace under the name they are written with, so any of
     * them beside an import of that name is one spelling with two answers. A binding in force is a
     * different thing and still wins over both: it is written inside a body, and what an import
     * says is what a name means where no binding answers it.
     */
    private static Validated validate(Ast.Module module) {
        Set<String> ownNames = new HashSet<>();
        for (Ast.FnDef fn : module.fns()) {
            ownNames.add(fn.name());
        }
        for (Ast.BehaviorDef b : module.behaviors()) {
            ownNames.add(b.name());
        }

        Set<String> declaredData = new HashSet<>();
        for (Ast.Def def : module.defs()) {
            declaredData.add(def.name());
        }

        Map<String, String> exposed = new HashMap<>();
        List<Ast.Import> kept = new ArrayList<>();
        List<Diagnostic> conflicts = new ArrayList<>();
        for (Ast.Import imp : module.imports()) {
            if (!Prelude.isQualifier(imp.module())) {
                kept.add(imp);   // an ordinary user-module import — resolved elsewhere
                continue;
            }
            for (String name : imp.names()) {
                String qualified = imp.module() + "." + name;
                if (!Prelude.isLibraryFunction(qualified)) {
                    throw CompileException.of(
                            Diagnostic.of(null, "check.import.notstdfn").title("check.module.title")
                                    .at(imp.pos()).args(name, imp.module()).build(),
                            "`" + name + "` is not a function in the standard library module `"
                                    + imp.module() + "` (spec §stdlib).");
                }
                if (declaredData.contains(name) || ownNames.contains(name)) {
                    conflicts.add(Diagnostic.of(null, "check.import.conflict")
                            .title("check.module.title").at(imp.pos()).args(name)
                            .hint("check.import.conflict.hint").build());
                    continue;   // the name is refused; what it means until then is the declaration
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
        return new Validated(exposed, kept, conflicts);
    }

    /**
     * {@code module} with its {@code import List ( ... )} lines dropped, having checked them.
     *
     * <p>What they brought in is answered by {@link #read} and settled where the bindings
     * are known. Nothing in the module is rewritten here: a name written bare is still written bare,
     * and what it means is one question asked in one place.
     */
    public static Ast.Module withoutLibraryImports(Ast.Module module, List<Ast.Import> kept) {
        if (kept.size() == module.imports().size()) {
            return module;
        }
        return new Ast.Module(module.name(), module.exposing(), module.exposedOutputs(),
                kept, module.defs(), module.behaviors(), module.fns(),
                module.examples(), module.fakes(), module.exampleFileTarget(), module.pos());
    }

}
