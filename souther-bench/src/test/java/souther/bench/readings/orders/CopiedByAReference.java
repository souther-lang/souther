package souther.bench.readings.orders;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Stream;

/**
 * Readers that take the order of a copy that no call in them makes: a method reference to the
 * copy is run by the library, and the call is made there.
 *
 * <p>Nothing here calls {@code Set.copyOf} or {@code Map.copyOf}, so a reading that began only
 * where a call is written would not begin here, and one that read the references without making
 * a copy of what they hand back would find nothing to follow.
 */
public final class CopiedByAReference {

    private CopiedByAReference() {}

    public static List<String> aSetMadeByAReferenceAndListed(List<String> values) {
        return new ArrayList<>(Stream.of(values).map(Set::copyOf).findFirst().orElseThrow());
    }

    public static List<String> aMapMadeByAReferenceAndListed(Map<String, String> values) {
        return new ArrayList<>(
                Stream.of(values).map(Map::copyOf).findFirst().orElseThrow().keySet());
    }
}
