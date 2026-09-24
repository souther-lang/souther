package souther.compiler.program;

import souther.compiler.abort.AbortSet;
import souther.compiler.abort.AbortSites;
import souther.compiler.core.Core;
import souther.compiler.core.Kernel;
import souther.compiler.core.KernelContract;
import souther.compiler.core.KernelContracts;
import souther.compiler.meta.ModulePath;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;

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
 * <p>What a behavior's rows said crosses with it ({@link CheckedBehavior#rows}). Those are what the
 * language says a behavior answers rather than a test of this compiler — a program whose rows do not
 * hold is not accepted — so an output emitting from this can hold what it emitted to what the model
 * owes, instead of to a test it wrote itself over inputs it picked itself. Whether an answer keeps a
 * row is asked of the language ({@link CheckedRow.SelfContained#holds}), and only of a row that
 * hands over values — one that does not says why instead, and there is nothing to ask.
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
 * read off the path declares, and that module is not among {@link #modules()}: nothing of it is
 * emitted by an output emitting this program, because the build that published it emitted it
 * already.
 *
 * <p>What a call to such a behavior reaches is another question, and {@link #behavior} answers it.
 * A call carries the identity resolution gave it and nothing else, and what an output emitting the
 * call needs — what the behavior takes, what it answers, and where its implementation comes from —
 * is asked with that identity. This compile read those declarations to check the body that names
 * one, so what is handed over is the reading the checker itself used.
 *
 * <p>What a name is a declaration of is another question, and it is asked with the identity rather
 * than through whoever declared it. {@link #declaration} answers what a value of that data is made
 * of, for every identity this compile resolved — its own modules', the language's, and a
 * dependency's alike, because this compile read the dependency's declarations to check the module
 * that names them, and an output laying such a value out needs exactly what the checker read. Who
 * declared it comes with the answer and decides who emits it.
 *
 * <p>{@link #modules()} enumerates and {@link #declaration} and {@link #behavior} resolve, and
 * those are two questions. What a module declares and what its behaviors are is what an output
 * emitting that module has to emit; what an identity is a declaration of, and what a call to one
 * reaches, is what an output laying out a value or emitting a call has to know. A reader made to
 * pick the owner before it could ask the second would be restating what its identity already
 * carries — and where what it names was declared elsewhere there is no module of the compilation to
 * pick at all.
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
     * The call boundary of every behavior this compile read the declaration of, by the identity a
     * call to it carries.
     *
     * <p>Handed in rather than built here, which the index above is not. A target is made before
     * the behavior that holds it: a row of a checked module states what it stood in for a
     * dependency with, and where that dependency's arguments stand is read off the dependency's own
     * target — so the targets are in hand before a module can be made at all. Built here from the
     * modules instead, it would be a second reading of what a behavior takes, and the reading a row
     * was written against would be the other one.
     *
     * <p>What holds the two together is that they are the same values. Every behavior of every
     * module here is filed under its identity, and it is the target that behavior holds and not a
     * copy of it.
     */
    private final Map<ValueName.Behavior, BehaviorTarget> behaviors;
    /**
     * What each kernel of the language was declared to take and answer, and every way a call to it
     * can end without a value instead.
     *
     * <p>Held once for the program and not on the calls that reach one. Which operation a call
     * reaches is a fact about that call, and so is what the call takes each argument as once the
     * signature's variables are settled for it; what the operation was declared to take and how it
     * can end without a value are facts about the language this program was checked with, and the
     * same for every call in every module — written onto each call site it would be one statement
     * copied as many times as the program happens to reach the library.
     */
    private final KernelContracts kernels;
    /**
     * Every way each {@code Core} site this program's outputs are asked to emit can end without a
     * value.
     *
     * <p>Classified once, over every behavior body and helper this program holds, rather than left
     * for an output to work out from {@code Core}'s own shape: that working-out is exactly what
     * left the JVM and a second backend each reading the same specification prose and writing down
     * their own list, which is what this program answers instead.
     */
    private final AbortSites aborts;

    CheckedProgram(List<CheckedModule> modules, List<CheckedData> languageDeclarations,
                   List<CheckedData> declaredOnThePath,
                   Map<ValueName.Behavior, BehaviorTarget> behaviors, KernelContracts kernels,
                   AbortSites aborts) {
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
        // No order is answered for: nothing here lists the behaviors of a program, and where one
        // stands among the others is how the modules were given rather than something the language
        // decided. What a reader does ask for is a behavior of a module, and a module answers that
        // in the order it declared them.
        this.behaviors = Map.copyOf(behaviors);
        // One fact, reached two ways, and held to that in both directions. A behavior of a checked
        // module is emitted through its module and called through its identity: the two routes
        // reaching different values is the state this index exists to make unwritable, and one
        // route reaching a behavior the other has never heard of is the same disagreement said the
        // other way round. Refused here rather than left to a reader to find.
        int declaredHere = 0;
        for (CheckedModule module : this.modules) {
            for (CheckedBehavior behavior : module.behaviors()) {
                if (this.behaviors.get(behavior.name()) != behavior.target()) {
                    throw new IllegalStateException("`" + behavior.name() + "` is called with a"
                            + " boundary that is not the one its module holds");
                }
                declaredHere++;
            }
        }
        int callableHere = 0;
        for (ValueName.Behavior called : this.behaviors.keySet()) {
            if (byName.containsKey(called.module())) {
                callableHere++;
            }
        }
        // Every behavior of a checked module is above, so the two can differ only by a behavior
        // this program can be called at that its own module does not declare. Counted rather than
        // asked of the module, which would be this same question one behavior at a time.
        if (callableHere != declaredHere) {
            throw new IllegalStateException("this program is callable at " + callableHere
                    + " behaviors of the modules it emits, which declare " + declaredHere);
        }
        this.kernels = Objects.requireNonNull(kernels,
                "a checked program is what the language it was checked with declares of its kernels");
        this.aborts = Objects.requireNonNull(aborts,
                "a checked program is what its own Core sites can end without a value for, too");
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
     * {@link CheckedData.WithFields#positionOf} refuses a name that is no field.
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
     * What a call to the behavior {@code name} reaches: what it takes, what it answers, and where
     * its implementation comes from.
     *
     * <p>Asked with the identity a call carries ({@link souther.compiler.core.Core.Reaches.ABehavior}),
     * which is what an output emitting that call holds. Whether the behavior is one of this
     * compile's own or one a module it read off the path declares is answered here rather than
     * decided by the reader: a call to either is emitted from the same three facts, and which of
     * them the caller has to emit an implementation for is {@link CheckedImplementation}'s answer.
     *
     * <p>Never a null and never an absence to interpret. Every behavior declared by a module this
     * compile checked or read off the path is here, whether or not anything in this program names
     * it — a snapshot holding what one walk of the bodies reached would be right about the calls
     * that walk thought to visit, and an output walking the same bodies again would be the second
     * place that decided what belongs.
     *
     * <p>What this is total over is those declarations, and not every value the Java type admits.
     * {@link ValueName.Behavior} is public, so an address nothing declares can be assembled; it is
     * a mistake at the reader, refused here for the reason {@link #declaration} refuses one.
     *
     * @throws IllegalArgumentException where no module this compile read declares {@code name}
     */
    public BehaviorTarget behavior(ValueName.Behavior name) {
        if (name == null) {
            throw new IllegalArgumentException("a behavior is asked for by its identity");
        }
        BehaviorTarget target = behaviors.get(name);
        if (target == null) {
            throw new IllegalArgumentException(
                    "no module this compile read declares the behavior `" + name + "`");
        }
        return target;
    }

    /**
     * What {@code kernel} was declared to take and to answer, and every way a call to it can end
     * without a value instead.
     *
     * <p>The declaration behind a call this program's bodies reach. A call says which operation it
     * reaches ({@link souther.compiler.core.Core.Reached.OfKernel}), and this answers what the
     * language declared of that operation for every call to it: the types as declared, with the
     * signature's type variables still open. It is not what one call takes. Each application settles
     * those variables, and the call says what it takes each argument as ({@link
     * souther.compiler.core.Core.CallSettlement.AtKernel#takes}), each argument standing at exactly
     * that type. An output reads that off the call and never substitutes this signature again.
     *
     * <p>An output building a boundary form for a call reads the declaration here — and reads {@link
     * KernelContract#aborts} here too, rather than deriving what a kernel can end without a value
     * for from its own reading of {@code souther-runtime} or of the specification prose the two
     * would otherwise have been read from separately.
     *
     * <p>Total over the kernels, and never a null. The language names a fixed set of them and a
     * snapshot holding fewer cannot be made, so there is no kernel a program can reach that this
     * has nothing for.
     *
     * <p>Asked of the program, because a program was checked against one version of the language.
     * A contract read from a library obtained some other way would be a second reading of what a
     * body was already checked against, and the two would agree for exactly as long as they were
     * the same version.
     */
    public KernelContract kernel(Kernel kernel) {
        return kernels.contractOf(kernel);
    }

    /**
     * Every {@link souther.compiler.abort.AbortKind} a run reaching {@code site} can end without a
     * value for.
     *
     * <p>{@code site} is any {@code Core} this program hands out, or a node under one: a body, a
     * clause a declared data holds its values to, a rule a behavior declares of its answer. Every
     * place the program hands one out is a site this answers for, whichever an output happens to
     * emit. A kernel site's answer already reads {@link #kernel}'s {@link KernelContract#aborts};
     * an {@code ensures} crossing's already reads {@link EnsuresEnforcement#aborts}; this is where
     * the rest — an arithmetic operator, an {@code unreachable}, a construction — answers the same
     * question.
     *
     * @throws IllegalArgumentException where {@code site} is not a {@code Core} this program holds
     */
    public AbortSet abortsAt(Core site) {
        return aborts.at(site);
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
