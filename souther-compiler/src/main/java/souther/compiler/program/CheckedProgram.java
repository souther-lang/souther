package souther.compiler.program;

import souther.compiler.core.Kernel;
import souther.compiler.core.KernelSignature;
import souther.compiler.meta.ModulePath;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.Collections;
import java.util.EnumMap;
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
 * <p>Only the modules this compile checked are here. A checked body may name a behavior a module
 * read off the path declares, and that module is not among {@link #modules()}: what the body
 * carries is the identity resolution gave it, and a call carries no signature and no body.
 *
 * <p>What a name is a declaration of is another question, and it is asked with the identity rather
 * than through whoever declared it. {@link #declaration} answers what a value of that data is made
 * of, for every identity this compile resolved — its own modules', the language's, and a
 * dependency's alike, because this compile read the dependency's declarations to check the module
 * that names them, and an output laying such a value out needs exactly what the checker read. Who
 * declared it comes with the answer and decides who emits it.
 *
 * <p>{@link #modules()} enumerates and {@link #declaration} resolves, and those are two questions.
 * What a module declares is what an output emitting that module has to emit; what an identity is a
 * declaration of is what an output laying out a value has to know. A reader made to pick the owner
 * before it could ask the second would be restating what its identity already carries — and where
 * the declaration is the language's there is no module of the compilation to pick at all.
 */
public final class CheckedProgram {

    private final List<CheckedModule> modules;
    private final Map<String, CheckedModule> byName;
    /**
     * Every declaration this compile resolved, by the identity that names it, in the order the
     * three worlds were read: this compilation's modules, the language's own, then what was read
     * off the path.
     *
     * <p>The one index everything here is read out of. A second collection holding some of these
     * again — the language's, say, for a reader that wants them listed — is a second membership to
     * keep true, and the day something is filed in one of them it is missing from the other.
     */
    private final Map<TypeSymbol.AtModule, Declared> declarations;
    /**
     * What each kernel of the language was declared to take and answer.
     *
     * <p>Held once for the program and not on the calls that reach one. Which operation a call
     * reaches is a fact about that call; what the operation accepts is a fact about the language
     * this program was checked with, and the same for every call in every module — written onto
     * each call site it would be one statement copied as many times as the program happens to reach
     * the library.
     */
    private final Map<Kernel, KernelSignature> kernels;

    CheckedProgram(List<CheckedModule> modules, List<CheckedData> languageDeclarations,
                   List<CheckedData> declaredOnThePath,
                   Map<Kernel, KernelSignature> kernels) {
        this.modules = List.copyOf(modules);
        Map<String, CheckedModule> named = new LinkedHashMap<>();
        for (CheckedModule module : this.modules) {
            named.put(module.name(), module);
        }
        this.byName = Map.copyOf(named);
        // Built here out of what the modules hold, rather than handed in beside them: an index
        // assembled somewhere else is a second statement of what this program declares, and the two
        // would agree until one of them was filled from a different reading.
        Map<TypeSymbol.AtModule, Declared> index = new LinkedHashMap<>();
        for (CheckedModule module : this.modules) {
            for (CheckedData declared : module.data()) {
                file(index, declared, DeclaredBy.A_MODULE);
            }
        }
        for (CheckedData declared : languageDeclarations) {
            file(index, declared, DeclaredBy.THE_LANGUAGE);
        }
        for (CheckedData declared : declaredOnThePath) {
            file(index, declared, DeclaredBy.A_MODULE_ON_THE_PATH);
        }
        // Ordered, because what is read out of it is read in an order: the language declares its
        // data in an order and a reader listing them is shown one. A map that kept none would show
        // an order nothing decided, which can differ between two runs of one compiler.
        this.declarations = Collections.unmodifiableMap(index);
        this.kernels = Collections.unmodifiableMap(new EnumMap<>(kernels));
    }

    /**
     * Files one declaration, and refuses a second at the same address.
     *
     * <p>An address belongs to one world. A module of a compilation may not be in the reserved
     * namespace, and a module of the compilation takes the name over one of the same name on the
     * path — so the three never meet, and one that did would be answered for by whichever was filed
     * last with nothing saying the other had been there.
     */
    private static void file(Map<TypeSymbol.AtModule, Declared> index, CheckedData declared,
                             DeclaredBy by) {
        Declared already = index.put(declared.name(), new Declared(declared, by));
        if (already != null) {
            throw new IllegalStateException("`" + declared.name() + "` is declared by "
                    + already.declaredBy() + " and by " + by);
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
     * <p>Never a null and never an absence to interpret. Every identity this compile resolved has
     * what a value of it is made of here, a dependency's included: this compile read that
     * dependency's declarations to check the module that names one, and an output laying such a
     * value out needs exactly what the checker read. Who declared it says who emits it and never
     * whether it can be laid out.
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
        Declared declared = declarations.get(name);
        if (declared == null) {
            throw new IllegalArgumentException(
                    "nothing this compile read declares `" + name + "`");
        }
        return declared;
    }

    /**
     * What {@code kernel} was declared to take and to answer.
     *
     * <p>The declaration behind a call this program's bodies reach. A call says which operation it
     * reaches ({@link souther.compiler.core.Core.Reached.OfKernel}) and every node carries the type
     * the checker settled for it, and those answer what arrived rather than what the callee accepts:
     * the two part company wherever a declared parameter is a type a value can arrive narrower than,
     * which a sum-typed parameter is. An output building a boundary form for a call reads it here.
     *
     * <p>Total over the kernels, and never a null. The language names a fixed set of them and the
     * library refuses to finish while one of them is declared nowhere, so there is no kernel a
     * program can reach that this has nothing for. A gap all the same is this compiler having read
     * its own library wrong, and is said rather than handed over as an absence to interpret.
     *
     * <p>Asked of the program, because a program was checked against one version of the language.
     * A signature read from a library obtained some other way would be a second reading of what a
     * body was already checked against, and the two would agree for exactly as long as they were
     * the same version.
     */
    public KernelSignature kernelSignature(Kernel kernel) {
        KernelSignature declared = kernels.get(kernel);
        if (declared == null) {
            throw new IllegalStateException(
                    "this program was checked against a library declaring nothing for " + kernel);
        }
        return declared;
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
     * <p>Read out of the index {@link #declaration} answers from, and not held beside it. Kept
     * beside it, the two would be a membership each and the day a declaration reached one of them
     * it would be missing from the other; taken from it, a language declaration is listed exactly
     * when it is answered for.
     *
     * <p>In the order the library declares them, which is the order they are filed in.
     */
    public List<CheckedData> languageDeclarations() {
        List<CheckedData> language = new ArrayList<>();
        for (Declared declared : declarations.values()) {
            if (declared.declaredBy() == DeclaredBy.THE_LANGUAGE) {
                language.add(declared.data());
            }
        }
        return List.copyOf(language);
    }
}
