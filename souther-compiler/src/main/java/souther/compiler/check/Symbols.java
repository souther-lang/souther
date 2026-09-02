package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.core.Kernel;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;

/**
 * What a name written in a module means, and what an identity is a declaration of, for a reader that
 * does not care which stage the declarations have reached.
 *
 * <p>Two carriers implement it and they are the two declaration worlds: {@link ResolvedSymbols}
 * reads declarations as resolution left them, {@link DerivedSymbols} as they were normalized. Which
 * one a reader is holding is which type it named, so a reader that has to be at a stage says so in
 * its signature and one that does not takes this.
 *
 * <p><b>A carrier answers in one form, and the two carriers answer in two.</b> That is the whole of
 * the difference between them, and it is a difference a reader either cares about — and names the
 * carrier it wants — or does not, because what it reads means the same either way: a declaration's
 * fields, what it includes, whether it is a newtype. What is refused is the other thing, one carrier
 * answering in two forms: a reader could then be handed a declaration in whichever form some
 * unrelated question came out in, and nothing it held would say which.
 *
 * <p>One declaration at a time. There is deliberately no {@code declarations()} and no table of
 * nodes here — either would let a reader take one stage's answers and read them back as declarations
 * nothing established, which is the thing the two worlds exist to stop; the derived world's table is
 * reached by naming {@link DerivedSymbols} and nowhere else.
 */
public sealed interface Symbols extends NameSense permits ResolvedSymbols, DerivedSymbols {

    /**
     * The declaration {@code name} is, in the form the carrier answering reads declarations in, or
     * null where nothing declares one.
     *
     * <p>One declaration, and what it says about itself. A reader wanting what a later stage worked
     * out for it — a product's boundary representation — asks the world that has it.
     */
    Hir.Def declaredNode(TypeSymbol name);

    /** The same, of an address. */
    Hir.Def declaredNode(TypeKey address);

    /** Whether {@code name} is declared by a module of this compilation — as opposed to a
     * declaration the language gives, which resolves and types like any other but belongs to no
     * module here. */
    boolean declaredByCompilation(TypeSymbol name);

    /** The same, of an address. */
    boolean declaredByCompilation(TypeKey address);

    /** The module being compiled. */
    String module();

    /** The library this module is compiled against. */
    Stdlib library();

    /**
     * The one walk the library publishes, which an output lowers as a loop rather than as a call.
     *
     * <p>Handed on rather than looked up. An output holds these symbols already and this is one
     * value of the language it was compiled against, so asking here is asking what it was given —
     * where reaching {@link #library()} would be an output that could put any question to the
     * library, which {@code TheBackendEmitsAgainstTheLanguageItWasHanded} keeps closed.
     */
    ValueName.Stdlib.Operation theWalk();

    /**
     * The one operation the library publishes that states elements are distinct, which an invariant
     * written over is a constraint rather than a call.
     *
     * <p>Handed on for the reason {@link #theWalk} is.
     */
    ValueName.Stdlib.Operation theDistinctnessPredicate();

    /**
     * Which kernel {@code operation} is declared to be, or null where it is not a kernel.
     *
     * <p>The question a pass asks when it recognises an operation by what it does rather than by
     * what it is called: a kernel is the language's own vocabulary and is the same whatever alias a
     * library publishes the operation under. Answered here rather than by reaching
     * {@link #library()} so that a reader holding these symbols has it — a {@code Kernel} is
     * {@code core}'s, so an output asking this is not naming the library.
     */
    Kernel kernelOf(ValueName.Stdlib.Operation operation);

    /** No module at all — for signatures written over primitives and type variables only. The
     *  library still arrives, because a signature over primitives may still name a library
     *  operation, and a caller with none of its own has one to hand. */
    static ResolvedSymbols none(Stdlib stdlib) {
        return ResolvedSymbols.none(stdlib);
    }

    /**
     * A lone module, compiled with nothing else in sight: bare names are its own definitions.
     *
     * <p>Resolved, because nothing has run over it: a caller holding a module and a library has the
     * declarations as resolution left them and no derivation to name.
     */
    static ResolvedSymbols of(Hir.Module m, Stdlib stdlib) {
        return ResolvedSymbols.of(m, stdlib);
    }
}
