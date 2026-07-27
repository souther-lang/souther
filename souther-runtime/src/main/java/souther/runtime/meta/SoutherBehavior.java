package souther.runtime.meta;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * A behavior, carried on the interface it generated.
 *
 * <p>{@link #injected} is the one thing here that is not Souther source. A behavior is an injection
 * target when its module declares it and writes no {@code let} for it, so a signature on its own
 * cannot say which of the two it is — the fn that decides is not carried, and there is no spelling
 * for the difference in the language. It is a flag rather than a new keyword.
 */
@Retention(RetentionPolicy.CLASS)
@Target(ElementType.TYPE)
public @interface SoutherBehavior {

    /** The signature: the {@code behavior} declaration as written for one with a signature, and the
     * computed one for a {@code >->} composition, which declares stages instead. Either way the
     * importing module reads a signature and never the stages behind it. */
    String signature();

    /** Whether the declaring module leaves this behavior to be injected. A module that names it as
     * a stage inherits it as a requirement of its own. */
    boolean injected();
}
