package souther.compiler.execute;

import souther.compiler.core.EnsuresEnforcement;
import souther.compiler.types.ValueName;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;

/**
 * What every behavior a module's rows reach declares of what it answers, and how the module that
 * declares it holds that.
 *
 * <p>Each answer is the declaring module's and not the module whose rows these are. A stand-in for a
 * behavior takes the place of its implementation, and what it owes is what that implementation owed:
 * a body checks its own answer, and what Java supplies is checked by the code calling it. That is a
 * fact about the behavior, so it is one answer however many places call the stand-in — the rows'
 * own module, or a stage another module declares that a composition hands the same stand-in to.
 *
 * <p>Every reachable behavior is here, the ones that state nothing included, so being absent means
 * that the behavior was not read and nothing else.
 *
 * @param held how the module declaring each reachable behavior holds what it declares
 */
public record DeclaredEnsures(Map<ValueName.Behavior, EnsuresEnforcement> held) {

    public DeclaredEnsures {
        // Copied, so what a reading was built with is what it keeps: a map a caller could still
        // change would put a second answer under a behavior after the first was read.
        held = Collections.unmodifiableMap(new LinkedHashMap<>(held));
    }
}
