package souther.runtime.meta;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * A behavior, carried on the interface it generated.
 *
 * <p>{@link #implementation} is the one thing here that is not Souther source. Where a behavior's
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

    /** Where the body comes from: {@code implemented}, {@code unimplemented} or {@code injected}.
     * A module that names an injected one as a stage inherits it as a requirement of its own. */
    String implementation();
}
