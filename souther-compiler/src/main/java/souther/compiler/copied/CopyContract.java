package souther.compiler.copied;

import java.util.Collections;
import java.util.SortedMap;
import java.util.TreeMap;

/**
 * What a module's classes offer another module to copy, and what they copied of other modules'
 * declarations — the copy half of what the module was built against.
 *
 * @param provides what each declaration of the module offers to be copied
 * @param requires what each declaration of another module the classes copied was when they copied it
 */
public record CopyContract(SortedMap<CopyTarget, CopyRecord> provides,
                           SortedMap<CopyTarget, CopyRecord> requires) {

    public CopyContract {
        provides = Collections.unmodifiableSortedMap(new TreeMap<>(provides));
        requires = Collections.unmodifiableSortedMap(new TreeMap<>(requires));
    }
}
