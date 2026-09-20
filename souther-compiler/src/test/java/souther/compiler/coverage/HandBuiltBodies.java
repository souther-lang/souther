package souther.compiler.coverage;

import souther.compiler.core.Core;

import java.util.LinkedHashMap;
import java.util.Map;

/**
 * The bodies a test builds by hand, for a source that writes behaviors and no value the backend
 * emits as a method.
 */
final class HandBuiltBodies {

    private HandBuiltBodies() {
    }

    /** {@code bodies} as the behaviors of the module {@code module}, calling no method. */
    static ModuleBodies ofBehaviors(String module, Map<String, Core> bodies) {
        return new ModuleBodies(module, new LinkedHashMap<>(bodies), new LinkedHashMap<>());
    }
}
