package souther.compiler.diag;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

/**
 * The sources a document writes the identities of, and what each of them is called.
 *
 * <p>A document for a machine carries what identifies a source rather than what to call it: an
 * identity is stable and is what makes two statements about the same file the same statement, and a
 * name is the shortest thing that tells one reader's files apart. Carrying the identity is right and
 * leaves the document unreadable on its own — nothing in it says which file a position in a list was.
 * So the identities are carried and the document explains them, and this is what collects the second
 * half while the first is being written.
 *
 * <p>Registered by the act of writing rather than gathered afterwards. A writer that gathered the
 * fields it knew about would be a list of the places an identity is written today, and the next field
 * to carry one would be outside it — which is the shape of the thing this is here to stop. Everything
 * that writes an identity into a document asks {@link #written} for the string to write, so a field
 * that is emitted is a field that is explained.
 *
 * <p>The table keeps the order the identities were first written in. Two runs over the same sources
 * write the same document and so build the same table, which is what a reader comparing two runs
 * needs; sorting would order a list of numbers as text and a list of URIs by nothing in particular.
 */
public final class DocumentSources {

    private final SourceNameResolver names;
    private final Set<String> referenced = new LinkedHashSet<>();

    public DocumentSources(SourceNameResolver names) {
        this.names = names;
    }

    /** The identity to write, recorded as one this document has to explain. */
    public String written(String sourceId) {
        referenced.add(sourceId);
        return sourceId;
    }

    /**
     * What each identity written so far is called.
     *
     * <p>The identities this document carries and not the sources the compile was handed. A document
     * that listed everything given to the compile would be saying what was compiled, which is a
     * second thing for it to be about; what a reader of this one needs is that every identity in
     * front of them can be looked up.
     */
    public Map<String, String> table() {
        Map<String, String> table = new LinkedHashMap<>();
        for (String sourceId : referenced) {
            table.put(sourceId, names.nameOf(sourceId));
        }
        return table;
    }
}
