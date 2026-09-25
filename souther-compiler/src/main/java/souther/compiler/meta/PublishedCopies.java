package souther.compiler.meta;

import souther.compiler.copied.CopyRecord;
import souther.compiler.copied.CopyTarget;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.SortedMap;
import java.util.TreeMap;

/**
 * Copies as {@link ModuleMetadata} writes them and {@link ModuleReadback} reads them: one entry per
 * declaration, holding its kind, its module, its name, the form it is copied in and what it is
 * copied as, every part counted the way {@link PublishedLinkages} counts one.
 *
 * <p>Written in the order of the declarations, so one set of copies is one set of entries.
 */
final class PublishedCopies {

    private PublishedCopies() {}

    static List<String> written(Map<CopyTarget, CopyRecord> copies) {
        List<String> out = new ArrayList<>(copies.size());
        new TreeMap<>(copies).forEach((target, record) -> out.add(
                PublishedRequirements.counted(target.kind())
                        + PublishedRequirements.counted(target.module())
                        + PublishedRequirements.counted(target.name())
                        + PublishedRequirements.counted(record.form().written())
                        + PublishedRequirements.counted(record.content())));
        return out;
    }

    /** The copies {@code entries} record, by the declaration — or null where one of them is not an
     *  entry this writes. */
    static SortedMap<CopyTarget, CopyRecord> read(List<String> entries) {
        SortedMap<CopyTarget, CopyRecord> out = new TreeMap<>();
        for (String entry : entries) {
            int[] at = {0};
            String kind = PublishedRequirements.counted(entry, at);
            String module = kind == null ? null : PublishedRequirements.counted(entry, at);
            String name = module == null ? null : PublishedRequirements.counted(entry, at);
            String form = name == null ? null : PublishedRequirements.counted(entry, at);
            String content = form == null ? null : PublishedRequirements.counted(entry, at);
            CopyTarget target = content == null ? null
                    : CopyTarget.readingWritten(kind, module, name);
            CopyRecord.Form readForm = target == null ? null : CopyRecord.Form.readingWritten(form);
            if (readForm == null || at[0] != entry.length()
                    || out.put(target, new CopyRecord(readForm, content)) != null) {
                return null;
            }
        }
        return out;
    }
}
