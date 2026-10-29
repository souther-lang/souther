package souther.compiler.partition;

import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

import souther.compiler.evaluate.BoundUnderEvaluation;
import souther.compiler.regex.CodeMap;
import souther.compiler.semantics.CaseMapping;

/**
 * A case conversion as the map on code points it is exactly one for ({@link CodeMap}), worked out
 * from the run time's own conversion the first time a conversion is asked of, and kept for the
 * rest: the map is a fact of the language and not of the model being read.
 */
final class CaseMaps {

    private static final Map<CaseMapping, CodeMap> MADE = new ConcurrentHashMap<>();

    private CaseMaps() {
    }

    /** The map {@code mapping} is on the code points it is exactly one for. */
    static CodeMap of(CaseMapping mapping) {
        CodeMap had = MADE.get(mapping);
        if (had == null) {
            had = CodeMap.of(text -> BoundUnderEvaluation.mapped(mapping, text));
            CodeMap raced = MADE.putIfAbsent(mapping, had);
            if (raced != null) {
                had = raced;
            }
        }
        return had;
    }
}
