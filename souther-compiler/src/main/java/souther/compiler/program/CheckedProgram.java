package souther.compiler.program;

import souther.compiler.meta.ModulePath;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

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
 * signature and no body, and a name carries no fields and no cases.
 *
 * <p>Which module a name belongs to is therefore asked before what it is. {@link #module} answers
 * null for a module this compile did not check, and a module answers null for a name it does not
 * declare, so the two absences are separate answers and neither reads as the other. Nothing here
 * shortens that into one question: shortened, a single null would carry both.
 */
public final class CheckedProgram {

    private final List<CheckedModule> modules;
    private final Map<String, CheckedModule> byName;

    CheckedProgram(List<CheckedModule> modules) {
        this.modules = List.copyOf(modules);
        Map<String, CheckedModule> named = new LinkedHashMap<>();
        for (CheckedModule module : this.modules) {
            named.put(module.name(), module);
        }
        this.byName = Map.copyOf(named);
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
}
