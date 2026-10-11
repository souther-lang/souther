package souther.compiler.check;

import souther.compiler.DefaultStdlib;
import souther.compiler.core.Core;
import souther.compiler.proof.EntriesFiledByKey;
import souther.compiler.types.ValueName;

import java.util.Map;
import java.util.Objects;
import java.util.function.Function;

/**
 * A map holding each element of a list under the key a closure makes of it, the later of two
 * elements of one key standing in place of the earlier.
 *
 * <p>Which operations answer one is read off the library's own bodies
 * ({@link EntriesFiledByKey}), so a call is one by what the operation does and not by its name.
 * An entry of the map is an element of the list: the value filed under a key is the last element
 * to have it, and no other value is in the map.
 *
 * @param walked the list whose elements are filed
 * @param key    the closure that answers the key an element is filed under
 */
public record AnIndexedMap(Core walked, Core.Block key) {

    public AnIndexedMap {
        Objects.requireNonNull(walked, "a map is filed from some list");
        Objects.requireNonNull(key, "an element is filed under what some closure makes of it");
    }

    /** Read once: the library is the same library for every module compiled. */
    private static final class Derived {
        private static final Map<ValueName.Stdlib.Operation, EntriesFiledByKey.Filing> FILINGS =
                EntriesFiledByKey.of(DefaultStdlib.get());
    }

    /**
     * What {@code container} is the answer of, where it is a map so built, or null where it is
     * not.
     *
     * @param blockOf the block a closure argument stands for, or null where it stands for none
     */
    public static AnIndexedMap of(Core container, Function<Core, Core.Block> blockOf) {
        if (!(Core.withoutStanding(container) instanceof Core.PreservedCall call)
                || !(call.operation() instanceof ValueName.Stdlib.Operation operation)) {
            return null;
        }
        EntriesFiledByKey.Filing filing = Derived.FILINGS.get(operation);
        if (filing == null) {
            return null;
        }
        Core.Block key = blockOf.apply(call.args().get(filing.keyArg()));
        return key == null || key.params().size() != 1 || key.params().getFirst().binding() == null
                ? null : new AnIndexedMap(call.args().get(filing.walkedArg()), key);
    }
}
