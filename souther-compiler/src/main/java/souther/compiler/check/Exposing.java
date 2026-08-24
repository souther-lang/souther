package souther.compiler.check;

import souther.compiler.Reserved;
import souther.compiler.ast.Ast;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;

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
     * the lines that could not do their job.
     *
     * <p>One value, because the first two are one fact. The module no longer says what its bare
     * names mean and the table is the only thing that does, so a caller holding the module holds the
     * table with it — wherever that module travels, and whether it was read from a source or off the
     * class path.
     *
     * <p>Every way of failing is answered rather than thrown, because each of them is one module's
     * mistake and not a reason to stop reading. Thrown, one escaped the question that asked for this
     * module and took every other file's diagnostics with it — an editor showed "the compiler could
     * not finish reading this file" for the whole workspace while the author was part-way through
     * writing a {@code let}. That was said here about the collision alone while the other two still
     * raised, and it was as true of them.
     */
    public record Checked(Ast.Module module, List<Scoping.Claim> claims,
                          List<Refusal> refused) {

        /**
         * Copied, because this is an answer a compilation remembers and an answer it remembers is a
         * value. What decides whether the work that read one has to be done again is whether the new
         * answer equals the old, so a caller able to reach into a remembered one could change what
         * every reader of it sees without anything being asked again.
         */
        public Checked {
            claims = List.copyOf(claims);
            refused = List.copyOf(refused);
        }
    }

    /**
     * What one {@code import List ( ... )} line could not do, as the check found it and before
     * anybody has decided what to say about it.
     *
     * <p>The data and not a diagnostic. Who reads this decides where the report goes and whether
     * there is one: a line in a source the author holds is said on that line, and the same failure
     * in a module read off the class path is a fact about an artifact, said where that module was
     * reached from. Built as a diagnostic here, the second reader would have to take one apart to
     * make the other, and the position it carries would be a line of a text nobody holds.
     *
     * <p>One arm, and it is a fact about the library and not about this module: the library
     * publishes no operation of that name, so the line claims nothing. Two lines claiming one
     * spelling, or a line claiming a spelling this module declares, are not here — those are
     * settled between claims ({@link Scoping}), where every claim is, and settling them here would
     * make what an author is told depend on whether the name happened to arrive from the library.
     */
    public sealed interface Refusal {

        /** The import line this was written on. */
        Ast.Import imp();

        /** The name it was to bring in. */
        String name();

        /** The standard library publishes no operation of that name in that module. */
        record NoSuchLibraryFunction(Ast.Import imp, String name) implements Refusal {}
    }

    /**
     * {@code module} read for its library imports: checked, dropped, and what they brought in.
     *
     * <p>Nothing in the module is rewritten. A name written bare is still written bare, and what it
     * means is one question asked in one place — {@link Scoping}, which settles this line's claims
     * beside every other line's.
     */
    public static Checked check(Ast.Module module) {
        Validated validated = validate(module);
        return new Checked(withoutLibraryImports(module, validated.kept()), validated.claims(),
                validated.refused());
    }

    /** What {@link #validate} answers, before the module is rebuilt around it. */
    private record Validated(List<Scoping.Claim> claims, List<Ast.Import> kept,
                             List<Refusal> refused) {}

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
        List<Scoping.Claim> claims = new ArrayList<>();
        List<Ast.Import> kept = new ArrayList<>();
        List<Refusal> refused = new ArrayList<>();
        for (Ast.Import imp : module.imports()) {
            if (!Reserved.isQualifier(imp.module())) {
                kept.add(imp);   // an ordinary user-module import — read where the universe is
                continue;
            }
            for (String name : imp.names()) {
                // The import line writes both halves of a library name: the module it names is the
                // alias, and each name in its list is the operation. What is brought in is that
                // pair, so nothing downstream has to take a spelling apart to get at either.
                ValueName.Stdlib operation = new ValueName.Stdlib(imp.module(), name);
                if (Prelude.isLibraryFunction(operation.qualified())) {
                    claims.add(new Scoping.Claim.Stands(imp, name, true,
                            new Scoping.Brought.ALibraryOperation(operation)));
                } else {
                    refused.add(new Refusal.NoSuchLibraryFunction(imp, name));
                    claims.add(new Scoping.Claim.DoesNot(imp, name, true));
                }
            }
        }
        return new Validated(claims, kept, refused);
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
