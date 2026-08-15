package souther.compiler.query;

import souther.compiler.ast.Ast;
import souther.compiler.check.ModuleUniverse;
import souther.compiler.types.ValueName;

import java.util.Map;
import java.util.Set;

/**
 * The modules of one compilation, as a {@link ModuleUniverse}.
 *
 * <p>One of the two ways a module is fetched, and the only thing that differs between a
 * compilation working out what its names mean and a reader working out the same of a module it read
 * back. What is done with what this answers is {@link souther.compiler.check.Scoping}'s, and is the
 * same either way.
 *
 * <p>Nothing is decided here. Each of the three answers is a question this compilation already had
 * one place to ask, and this is where the three of them are put in the shape a scope is assembled
 * from — which is why the module and the library names it may write bare come back as one value:
 * they are one reading, and answered separately one of them was answered emptily.
 */
public record CompilationUniverse(Db db) implements ModuleUniverse {

    /** The universe this compilation is. */
    public static ModuleUniverse over(Db db) {
        return new CompilationUniverse(db);
    }

    @Override
    public InSight module(String name) {
        Set<String> broken = db.ask(new Front.Broken()).value();
        if (broken != null && broken.contains(name)) {
            return InSight.UNREADABLE;   // the file that will not parse reports its own error
        }
        Ast.Module m = db.ask(new Front.Available(name)).value();
        if (m == null) {
            // Knowing a name and having a module to give under it are two questions. A module the
            // path holds and this compilation refuses is one an author named wrongly, not one
            // nobody has heard of, and told both they are left with two reports that cannot both
            // be true.
            Set<String> known = db.ask(new Front.ModuleNames()).value();
            return known != null && known.contains(name) ? InSight.UNREADABLE : InSight.UNKNOWN;
        }
        Map<String, ValueName.Stdlib> library = db.ask(new Front.LibraryNames(name)).value();
        return new InSight.Read(m, library == null ? Map.of() : library);
    }
}
