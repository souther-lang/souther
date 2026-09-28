package souther.runtime.meta;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * A behavior, carried on the interface it generated.
 *
 * <p>{@link #signatureFrom} and {@link #implementation} are not Souther source. A composition
 * declares stages rather than a signature, and the stages are not published, so what its signature
 * is written out as reads like a declaration; the first says whether it is one.
 *
 * <p>Where a behavior's
 * body comes from is decided from the {@code let} the module writes and the {@code depends on} the
 * declaration carries, and the fn is not published — so a signature on its own cannot say which of
 * the three states this is, and the state travels beside it. A word rather than a flag: a reader
 * that got a boolean had two answers to give for three declarations, and put a behavior nobody has
 * written yet under the one Java supplies.
 */
@Retention(RetentionPolicy.CLASS)
@Target(ElementType.TYPE)
public @interface SoutherBehavior {

    /** The signature: the {@code behavior} declaration as written for one with a signature, and the
     * computed one for a {@code >->} composition, which declares stages instead. Either way the
     * importing module reads a signature and never the stages behind it. */
    String signature();

    /** Where {@link #signature} comes from: {@code declared} for a behavior that wrote it, and
     * {@code composed} for a {@code >->} composition, whose signature is what its stages compute and
     * whose parameter names were made up to write it out as source. */
    String signatureFrom();

    /** Where the body comes from: {@code implemented}, {@code unimplemented} or {@code injected}.
     * A module that names an injected one as a stage inherits it as a requirement of its own. */
    String implementation();

    /** What constructing the behavior requires injected, in the order its constructor takes them,
     * each written as the declaring module and the name, counted. Worked out by the module that
     * declares the behavior: a composition's comes from stages that are not published, so a reader
     * could not work it out again. An injection target is not constructed here and writes none.
     * No default: a writer that says nothing about it has not said the list is empty. */
    String[] requirements();
}
