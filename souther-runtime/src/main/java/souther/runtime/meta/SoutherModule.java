package souther.runtime.meta;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * The module-level declarations of a compiled Souther module, carried on its generated
 * {@code $Module} class so another project can import the module from a jar.
 *
 * <p>What each definition says lives on that definition's own class ({@link SoutherData},
 * {@link SoutherBehavior}); this names them, so a reader walks a list instead of enumerating a
 * package. Retention is {@code CLASS}: an annotation processor reads it off the compile classpath
 * through {@code Elements}, and the CLI through the class file, neither of which needs it at run
 * time.
 */
@Retention(RetentionPolicy.CLASS)
@Target(ElementType.TYPE)
public @interface SoutherModule {

    /** The version of the boundary between a compiled module and the modules that import it. A
     * reader refuses a module whose number is not its own; 0.x promises nothing across it. What the
     * number stands for is decided where that boundary is emitted, not here. */
    int compat();

    /** The compiler that produced this module, for the diagnostic that reports a {@link #compat}
     * mismatch. Nothing is decided by it. */
    String compiler();

    /** The module name, as written in its {@code module} header. */
    String name();

    /** The {@code module … exposing ( … )} line as written. It carries more than the exposed names —
     * a composition declares its output there — so it travels as written rather than as a list. */
    String header();

    /** The module's {@code import} lines, verbatim, standard-library ones included: the definitions
     * are carried as they were written, so the names in them resolve in the scope they were written
     * in. */
    String[] imports() default {};

    /** The data definitions of this module. Each names a class of this module that carries its own
     * {@link SoutherData}; a name listed here always has one. Every definition is listed, not only
     * the exposed ones: an exposed type's field may name a type that is not itself exposed, and
     * {@code exposing} remains the gate on what may be imported. */
    String[] types() default {};

    /** This module's behaviors, by the name each was declared under. The class carrying a behavior's
     * {@link SoutherBehavior} is the one that name is emitted under, which is not always the name
     * itself (spec §jvm-behavior). */
    String[] behaviors() default {};

    /** The helper {@code let}s an invariant of this module calls, verbatim. An invariant is part of
     * what a type is, so it has to be readable where the type is imported, and it cannot be read
     * without the helpers it names. Helpers no invariant reaches are not carried. */
    String[] invariantHelpers() default {};
}
