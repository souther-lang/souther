package souther.compiler.program;

import souther.compiler.meta.ModulePath;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * A Souther program the compiler checked, for an output that lives outside this compiler.
 *
 * <p>What crosses is what the language compiler decided: what each module declares, what each
 * behavior takes and answers, where its implementation comes from, and — where the implementation
 * is written here — the {@link souther.compiler.core.Core} the checker typed or the
 * {@link souther.compiler.core.Composition} it settled. An output emits from those. It does not
 * recover a body from source, resolve a callee, or infer a type a second time; two compilers that
 * did would disagree about a decision that is the language's and was made once.
 *
 * <p>How this compiler works out its answers is not here. There is no {@code Db} on this object and
 * none behind it: what a query was asked, and which key held which answer, is how
 * {@code souther-compiler} computes and invalidates, not part of the contract with another
 * artifact. This is a snapshot — taken when it was made, and unchanged by anything the compilation
 * that made it goes on to do.
 *
 * <p>Nor is any decision about representing these on some machine. A JVM descriptor, a class name,
 * a local slot, a Wasm block — those belong to whichever output is emitting, and two outputs may
 * settle them differently without the program meaning anything different.
 *
 * <p>What this is says nothing of a machine; getting one still runs one. The language accepts a
 * program only where its constant constructions hold and its rows do, both of which are decided by
 * running the program — which today means running the classes the JVM backend emits (ADR-0032). So
 * a program the JVM cannot emit is refused here whether or not the language had anything against
 * it, and an output that is not the JVM inherits that. The snapshot itself carries none of it: what
 * carries it is how an accepted one is obtained, and that moves when what acceptance runs a program
 * with stops being named by the thing that asks.
 *
 * <p>Only the modules this compile checked are here. A checked body may name something a module
 * read off the path declares — a behavior it calls, a data whose field it reads — and that module
 * is not among {@link #modules()}. What the body carries is the identity resolution gave it; what
 * the declaring module says about that identity is not part of this snapshot. A call carries no
 * signature and no body.
 *
 * <p>What a name is a declaration of is asked with the identity, rather than through whoever
 * declared it. {@link #declaration} is the whole of that: it answers what a value of a data is made
 * of where this snapshot holds the declaration, and says the declaration is a module off the path's
 * where it does not — so a name whose fields and cases are not here is one that says so, and not
 * one that reads as no declaration at all. A reader that chose the owner first would be
 * deciding, of every identity it holds, which world to ask — and the reserved namespace is a world
 * with no module of the compilation in it, so the reader that chose had nothing to choose.
 *
 * <p>{@link #modules()} enumerates and {@link #declaration} resolves, and those are two questions.
 * What a module declares is what an output emitting that module has to emit; what an identity is a
 * declaration of is what an output laying out a value has to know. A module answering the second
 * about its own would be the same answer reachable two ways, and the way through the module is the
 * one that has no answer for what the language declares.
 */
public final class CheckedProgram {

    private final List<CheckedModule> modules;
    private final Map<String, CheckedModule> byName;
    /** Every declaration this snapshot holds, by the identity that names it — the one index both
     *  {@link #declaration} and {@link #languageDeclarations} are read out of. Two indexes, one per
     *  world, would be two places for a declaration to be filed and one of them to be looked in. */
    private final Map<TypeSymbol.AtModule, Declared.Available> declarations;
    private final List<CheckedData> languageDeclarations;
    private final Set<TypeSymbol.AtModule> onThePath;

    CheckedProgram(List<CheckedModule> modules, List<CheckedData> languageDeclarations,
                   Set<TypeSymbol.AtModule> onThePath) {
        this.modules = List.copyOf(modules);
        Map<String, CheckedModule> named = new LinkedHashMap<>();
        for (CheckedModule module : this.modules) {
            named.put(module.name(), module);
        }
        this.byName = Map.copyOf(named);
        // Built here out of what the modules hold, rather than handed in beside them: an index
        // assembled somewhere else is a second statement of what this program declares, and the two
        // would agree until one of them was filled from a different reading.
        Map<TypeSymbol.AtModule, Declared.Available> index = new LinkedHashMap<>();
        for (CheckedModule module : this.modules) {
            for (CheckedData declared : module.data()) {
                index.put(declared.name(), new Declared.Available(declared, DeclaredBy.A_MODULE));
            }
        }
        List<CheckedData> ofTheLanguage = new ArrayList<>();
        for (CheckedData declared : languageDeclarations) {
            Declared.Available already = index.put(declared.name(),
                    new Declared.Available(declared, DeclaredBy.THE_LANGUAGE));
            if (already != null) {
                // A module of this compilation and the language both declaring one address is the
                // reserved namespace having been taken, which is refused where a module is read.
                // Reaching here means it was not, and the second answer would silently be the one
                // every reader got.
                throw new IllegalStateException(
                        "`" + declared.name() + "` is declared by the language and by a module");
            }
            ofTheLanguage.add(declared);
        }
        this.declarations = Map.copyOf(index);
        this.languageDeclarations = List.copyOf(ofTheLanguage);
        this.onThePath = Set.copyOf(onThePath);
        for (TypeSymbol.AtModule elsewhere : this.onThePath) {
            if (this.declarations.containsKey(elsewhere)) {
                // The two are answers to one question and an identity that is both would be
                // answered by whichever was consulted first — which would make the order the
                // lookup happens to try into a rule about what a declaration is.
                throw new IllegalStateException("`" + elsewhere
                        + "` is declared here and read off the path");
            }
        }
    }

    /**
     * Checks {@code sources} together and takes what came of it.
     *
     * <p>Answering with one of these says the program checked. A compile that did not raises what
     * it found instead: there is no half-checked program to hand over, and a reader that wants to
     * say something either way is asking a different question than this.
     *
     * @throws souther.compiler.diag.CompileException where the program did not check
     */
    public static CheckedProgram of(List<String> sources) {
        return of(sources, ModulePath.EMPTY);
    }

    /**
     * As {@link #of(List)}, resolving an import that names no module among {@code sources} against
     * {@code path} — the compiled modules of the projects this one depends on.
     *
     * @throws souther.compiler.diag.CompileException where the program did not check
     */
    public static CheckedProgram of(List<String> sources, ModulePath path) {
        return CheckedProgramAssembler.of(sources, path);
    }

    /** The modules this compile checked, in the order they were given. */
    public List<CheckedModule> modules() {
        return modules;
    }

    /** The module called {@code name}, or null where this compile did not check one. */
    public CheckedModule module(String name) {
        return byName.get(name);
    }

    /**
     * What the declaration {@code name} identifies is made of, or that it is in a module off the
     * path.
     *
     * <p>Asked with the identity a body carries, which is what a reader laying out a value holds.
     * Whoever declared it — a module of this compile, or the language, in the reserved namespace
     * where no compilation declares anything — is answered here rather than chosen by the reader,
     * so a value of a data the language gives is read exactly as a value of a module's own is.
     *
     * <p>Never a null and never an absence to interpret. Every identity this compile resolved is
     * one of the two arms, and the arms are told apart by what was decided rather than by what was
     * left over: {@link Declared.OnThePath} is answered because this compile read that module off
     * the path and found the name among what it declares, not because nothing else answered.
     *
     * <p>What this is total over is the identities this compile resolved, and not every value the
     * Java type admits. An identity is minted where a declaration world says one is at an address,
     * so an address nothing declares is a mistake at the reader — refused here, for the reason
     * {@link CheckedData.Product#positionOf} refuses a name that is no field.
     *
     * @throws IllegalArgumentException where nothing this compile read declares {@code name}
     */
    public Declared declaration(TypeSymbol.AtModule name) {
        if (name == null) {
            throw new IllegalArgumentException("a declaration is asked for by its identity");
        }
        Declared.Available available = declarations.get(name);
        if (available != null) {
            return available;
        }
        if (onThePath.contains(name)) {
            return new Declared.OnThePath();
        }
        throw new IllegalArgumentException(
                "nothing this compile read declares `" + name + "`");
    }

    /**
     * What the language itself declares, which no module of any compilation does.
     *
     * <p>Here so that an output that has to materialise them has the list rather than a walk of its
     * own. Which declarations the language gives is a fact about the language this program was
     * checked with; an output that collected them by walking the bodies it was given would be right
     * about the ones its walk reached, and a declaration nothing in this program happens to name
     * would be one it never emitted.
     *
     * <p>The same declarations {@link #declaration} answers with under {@link DeclaredBy#THE_LANGUAGE},
     * read out of the one index rather than gathered again.
     */
    public List<CheckedData> languageDeclarations() {
        return languageDeclarations;
    }
}
