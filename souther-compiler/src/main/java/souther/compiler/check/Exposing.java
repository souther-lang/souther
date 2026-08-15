package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.msg.ImportMessage;
import souther.compiler.types.ValueName;

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
 * <p>What the imports bring in is answered as a table and nothing in the module is rewritten. A name
 * written bare stays written bare, and what it means where it is written is settled once, by
 * resolution, with the bindings in force — an import is the last thing consulted and a binding in
 * force wins over it. A declaration of that name does not shadow it: the two are a conflict, refused
 * on the import line, and the declaration standing as the name's meaning after that is what recovery
 * does with a module that will not be emitted. The {@code import List ( ... )} lines are then
 * dropped, having been checked.
 *
 * <p>The table and the module without those lines are one answer ({@link #check}), because a module
 * that has had them dropped is unreadable without it. There is no way to take the second and leave
 * the first: a reader of a module off the class path did exactly that, and an invariant that called
 * a name its module imported bare then resolved against nothing in every project but the one that
 * wrote it.
 *
 * <p>It mirrors Elm's {@code import List exposing (map)}: the qualified access always works, and the
 * import merely lets a name be written without its qualifier. A name exposed from two libraries at
 * once is ambiguous and rejected — qualify it instead.
 */
public final class Exposing {

    private Exposing() {}

    /**
     * A module with its {@code import List ( ... )} lines dropped, what those lines brought in, and
     * the ones that name something the module already declares.
     *
     * <p>One value, because the first two are one fact. The module no longer says what its bare
     * names mean and the table is the only thing that does, so a caller holding the module holds the
     * table with it — wherever that module travels, and whether it was read from a source or off the
     * class path.
     *
     * <p>A collision is answered rather than thrown because it is one module's mistake and not a
     * reason to stop reading. Thrown, it escaped the question that asked for this module and took
     * every other file's diagnostics with it — an editor showed "the compiler could not finish
     * reading this file" for the whole workspace while the author was part-way through writing a
     * {@code let}.
     */
    public record Checked(Ast.Module module, Map<String, ValueName.Stdlib> exposed,
                          List<Diagnostic> conflicts) {}

    /**
     * {@code module} read for its library imports: checked, dropped, and what they brought in.
     *
     * <p>Nothing in the module is rewritten. A name written bare is still written bare, and what it
     * means is one question asked in one place — resolution, against {@link Checked#exposed}.
     */
    public static Checked check(Ast.Module module) {
        Validated validated = validate(module);
        return new Checked(withoutLibraryImports(module, validated.kept()), validated.exposed(),
                validated.conflicts());
    }

    /** What {@link #validate} answers, before the module is rebuilt around it. */
    private record Validated(Map<String, ValueName.Stdlib> exposed, List<Ast.Import> kept,
                             List<Diagnostic> conflicts) {}

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

        Map<String, ValueName.Stdlib> exposed = new HashMap<>();
        List<Ast.Import> kept = new ArrayList<>();
        List<Diagnostic> conflicts = new ArrayList<>();
        for (Ast.Import imp : module.imports()) {
            if (!Prelude.isQualifier(imp.module())) {
                kept.add(imp);   // an ordinary user-module import — resolved elsewhere
                continue;
            }
            for (String name : imp.names()) {
                // The import line writes both halves of a library name: the module it names is the
                // alias, and each name in its list is the operation. What is brought in is that pair,
                // so nothing downstream has to take a spelling apart to get at either.
                ValueName.Stdlib operation = new ValueName.Stdlib(imp.module(), name);
                String qualified = operation.qualified();
                if (!Prelude.isLibraryFunction(qualified)) {
                    throw CompileException.of(Diagnostic.at(imp.pos())
                            .say(new ImportMessage.NameIsNotAStandardLibraryFunction(
                                    name, imp.module()))
                            .build());
                }
                if (declaredData.contains(name) || ownNames.contains(name)) {
                    conflicts.add(Diagnostic.at(imp.pos())
                            .say(new ImportMessage.ImportedNameCollidesWithADeclaration(name))
                            .hint(new ImportMessage.RenameOrQualifyTheCollidingName())
                            .build());
                    continue;   // the name is refused; what it means until then is the declaration
                }
                ValueName.Stdlib prior = exposed.putIfAbsent(name, operation);
                if (prior != null && !prior.equals(operation)) {
                    throw CompileException.of(Diagnostic.at(imp.pos())
                            .say(new ImportMessage.NameIsPublishedByTwoModules(
                                    name, prior.qualified(), qualified))
                            .build());
                }
            }
        }
        return new Validated(exposed, kept, conflicts);
    }

    private static Ast.Module withoutLibraryImports(Ast.Module module, List<Ast.Import> kept) {
        if (kept.size() == module.imports().size()) {
            return module;
        }
        return new Ast.Module(module.name(), module.exposing(), module.exposedOutputs(),
                kept, module.defs(), module.behaviors(), module.fns(), module.takenOn(),
                module.examples(), module.fakes(), module.exampleFileTarget(), module.pos());
    }

}
