package souther.compiler.program;

import souther.compiler.core.Core;
import souther.compiler.types.ValueName;

/**
 * The entry a module publishes for one of its values, through which another module reaches it.
 *
 * <p>Not the value's own body ({@link CheckedValue#body()}), which is the executable home built in
 * the declaring module. This is the nullary bridge ADR-0074 describes: a definition taking nothing
 * and answering with the value, so that a reader in another module calls it rather than holding a
 * copy of the value's dependencies. Its {@link #body()} is a reference to the value and nothing
 * else.
 *
 * <p>Always nullary, so there is no {@code parameters()} here to hold empty by construction — the
 * shape of this type says what {@link souther.compiler.check.ValueEntries} builds, rather than a
 * reader having to ask an empty list the same question every call site already answers.
 */
public final class CheckedValueEntry {

    private final ValueName.Helper value;
    private final Core body;

    CheckedValueEntry(ValueName.Helper value, Core body) {
        this.value = value;
        this.body = body;
    }

    /** The value this entry publishes. */
    public ValueName.Helper value() {
        return value;
    }

    /** The nullary bridge body, as checked: a reference to {@link #value()} and nothing else. */
    public Core body() {
        return body;
    }

    @Override
    public String toString() {
        return "entry(" + value + ")";
    }
}
