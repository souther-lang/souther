package souther.compiler.meta;

import souther.compiler.ast.Ast;
import souther.compiler.check.Scoping;

import java.util.ArrayList;
import java.util.List;

/**
 * What a refused scope is, as facts about the artifact it was assembled for.
 *
 * <p>The other side of the reporting a compilation does with the same refusals, and here for the
 * reason that one is there: assembling a scope answers what a module's names can mean and which of
 * them could not be settled, and that answer is the same wherever the module came from. Saying it
 * to somebody is not. A module of a compilation has an author holding the file, who is sent to the
 * line; a module read back off an artifact has no such reader, and a refusal there is a fact about
 * the artifact said to whoever put it on the path.
 *
 * <p>Every refusal is projected and none is dropped. Which reason a reader is given used to follow
 * from which stage of the reading happened to find it — a library import line was read before any
 * other module was in sight, so its refusals had a name, and every refusal that needed the
 * surrounding modules had nowhere to be said and became a module that is unreadable for no stated
 * reason. So the projection is a switch over every refusal there is, with nothing to fall through
 * to: a rule added to the assembly is one this boundary has to say something about.
 *
 * <p>The place goes and the fact stays. A refusal carries the {@code import} line or the
 * declaration it is about — an AST node, with the place in the published text it was parsed from —
 * and that place is a line of a text nobody holds.
 */
final class ScopeRefusals {

    private ScopeRefusals() {}

    /**
     * What the artifact is refused for, given the refusals assembling its scope found.
     *
     * <p>Its declarations before its import lines, where both were refused. Not the order they were
     * found in — they come out of one assembly and have no order between them — but the order the
     * two questions depend on each other in: what a module declares is settled by what it wrote,
     * and whether a line may bring a name in is asked against those declarations. Answered the
     * other way round, a reader is told about a line held against a set of declarations this
     * compiler has already refused. It is the rule the reading before this one already goes by,
     * which indexes what a module declares before it reads what its lines bring in.
     *
     * @param refused what assembling the scope refused, which is never empty — a scope that refused
     *        nothing is a module that was read, and there is no failure to name for one
     */
    static Readback.Failure of(List<Scoping.Refusal> refused) {
        if (refused.isEmpty()) {
            throw new IllegalArgumentException(
                    "a scope that refused nothing is a module that was read");
        }
        List<Readback.DeclarationRejection> declarations = new ArrayList<>();
        List<Readback.Exposure> lines = new ArrayList<>();
        for (Scoping.Refusal each : refused) {
            switch (each) {
                case Scoping.Refusal.TakesTheLibraryQualifier(Ast.Def def) ->
                        declarations.add(new Readback.DeclarationRejection
                                .TakesTheLibraryQualifier(def.name()));
                case Scoping.Refusal.ALetAndADataShareASpelling(Ast.FnDef fn) ->
                        declarations.add(new Readback.DeclarationRejection
                                .ALetAndADataShareASpelling(fn.name()));
                case Scoping.Refusal.NoSuchModule(Ast.Import imp) ->
                        lines.add(new Readback.Exposure.NoSuchModule(imp.module()));
                case Scoping.Refusal.NotExposed(Ast.Import imp, String name) ->
                        lines.add(new Readback.Exposure.NotExposed(imp.module(), name));
                case Scoping.Refusal.NoSuchName(Ast.Import imp, String name) ->
                        lines.add(new Readback.Exposure.NoSuchName(imp.module(), name));
                case Scoping.Refusal.AliasTaken(Ast.Import imp, String takenBy) ->
                        lines.add(new Readback.Exposure.AliasTaken(imp.module(), imp.alias(),
                                takenBy));
                case Scoping.Refusal.BroughtTwice(Ast.Import imp, String name, Ast.Import earlier) ->
                        lines.add(new Readback.Exposure.BroughtTwice(imp.module(), name,
                                earlier.module()));
                case Scoping.Refusal.CollidesWithADeclaration(Ast.Import imp, String name) ->
                        lines.add(new Readback.Exposure.CollidesWithADeclaration(imp.module(),
                                name));
            }
        }
        if (!declarations.isEmpty()) {
            return new Readback.Failure.InvalidDeclarations(declarations.get(0),
                    declarations.subList(1, declarations.size()));
        }
        return new Readback.Failure.InvalidExposure(lines.get(0),
                lines.subList(1, lines.size()));
    }
}
