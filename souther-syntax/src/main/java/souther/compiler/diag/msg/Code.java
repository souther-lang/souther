package souther.compiler.diag.msg;

import souther.compiler.diag.DiagnosticCode;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * The rule a {@link Message} reports.
 *
 * <p>Several messages carry one code: a rule broken in two ways is two wordings and one code, and
 * the reader looks the code up either way. What no message may do is carry none, which is what the
 * build holds the messages to.
 */
@Retention(RetentionPolicy.RUNTIME)
@Target(ElementType.TYPE)
public @interface Code {
    DiagnosticCode value();
}
