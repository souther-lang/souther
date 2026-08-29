package souther.compiler.query;

import souther.compiler.ast.Ast;
import souther.compiler.check.ModuleUniverse;
import souther.compiler.check.Registry;
import souther.compiler.check.Scoping;
import java.util.List;

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
 * <p>Nothing is decided here. Each answer is a question this compilation already had one place to
 * ask, and this is where they are put in the shape a scope is assembled from — which is why the
 * module and the library names it may write bare come back as one value: they are one reading, and
 * answered separately one of them was answered emptily.
 *
 * <p>What it answers is what this compilation will let something be built on. That is not the same
 * as what it has parsed: a module in an import cycle has been read and is one nothing may be built
 * on, so it is unreadable here, and the declarations {@code Resolve} is given read it the same way.
 * Which modules a module names is a different question again, answered off what it wrote — a cycle
 * is found by following those names, so an answer that stopped at a module in one could not find
 * the second half of it.
 */
public record CompilationUniverse(Db db) implements ModuleUniverse {

    /** The universe this compilation is. */
    public static ModuleUniverse over(Db db) {
        return new CompilationUniverse(db);
    }

    /**
     * The module a scope is being assembled for, as this compilation reads it — or null where there
     * is no scope to assemble.
     *
     * <p>The one place the module and the library names its own import lines let it write bare are
     * put together on this side. Read here and not in {@link #module}, because it is a fact about
     * the module being scoped and about no other: read of every module named, an edit to a library
     * import line anywhere would be a reason to assemble every importing module's scope again.
     */
    public static Scoping.Subject subject(Db db, String name) {
        // The module itself, which only the module being scoped is read from. A neighbour is what
        // was settled about it, asked one name at a time; a universe that handed its text over
        // would let every walk work the same facts out again.
        Ast.Module m = db.ask(new Front.Available(name)).value();
        if (m == null) {
            return null;
        }
        Registry.Declared<Ast.Def> declared = declaredBy(db, name);
        if (declared == null) {
            return null;
        }
        List<Scoping.Claim> library = db.ask(new Front.LibraryClaims(name)).value();
        // The three are one reading. A module whose table this compilation cannot answer is not one
        // a scope can be assembled for: answered emptily instead, every bare name its import lines
        // brought in would denote nothing.
        return library == null ? null : new Scoping.Subject(m, declared, library);
    }

    /**
     * What a registry has under {@code name}, or null where this compilation will let nothing be
     * built on it.
     *
     * <p>Both halves asked of the questions that already answer them — a name written twice is
     * refused once, where declarations are indexed, and what a module exposes is read off its
     * source in one place ({@link Front.Exposes}). Worked out here instead, the {@code exposing}
     * list would have a second reader, which is what left one walk taking {@code Amount.decoder}
     * for a name and another taking it for {@code Amount}.
     */
    private static Registry.Declared<Ast.Def> declaredBy(Db db, String name) {
        // Asked only once the caller has a module to ask it of, which is why every caller reads
        // Front.Available first. Whether a module is in a cycle is worked out over the whole
        // workspace, and a name nothing here has is not a question about the shape of the
        // workspace — an import of a misspelt module would otherwise put every module's imports on
        // the far side of this one's answer.
        Answer<Map<String, Ast.Def>> declarations = db.ask(new Names.Declarations(name));
        if (!declarations.present()) {
            return null;
        }
        Set<String> exposed = db.ask(new Front.Exposes(name)).value();
        return exposed == null ? null : new Registry.Declared<>(declarations.value(), exposed);
    }

    @Override
    public InSight module(String name) {
        Ast.Module m = db.ask(new Front.Available(name)).value();
        if (m != null) {
            // What this compilation has under that name, asked of the questions that answer it —
            // so that what a scope says a name denotes and what the declarations say is declared
            // there cannot disagree. A module in an import cycle has nothing to give here: what it
            // declares rests on the module that rests on it.
            Registry.Declared<Ast.Def> declared = declaredBy(db, name);
            if (declared != null) {
                return InSight.Read.of(m, declared);
            }
        }
        // Nothing to give — and now why. A file the caller held back reports its own error, so an
        // importer of it is left alone rather than told the module is unknown. Asked after the
        // reading and not before it: what is wrong with a source says nothing about a module of
        // that name the path holds, which is there to be read whatever this compilation was handed.
        Set<String> broken = db.ask(new Front.Broken()).value();
        if (broken != null && broken.contains(name)) {
            return InSight.UNREADABLE;
        }
        // Knowing a name and having a module to give under it are two questions. A module the path
        // holds and this compilation refuses is one an author named wrongly, not one nobody has
        // heard of, and told both they are left with two reports that cannot both be true.
        Set<String> known = db.ask(new Front.ModuleNames()).value();
        return known != null && known.contains(name) ? InSight.UNREADABLE : InSight.UNKNOWN;
    }
}
