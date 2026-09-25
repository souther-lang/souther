package souther.compiler.meta;

import souther.compiler.jvm.LinkageProjection;
import souther.compiler.jvm.LinkageRecord;
import souther.compiler.jvm.LinkageTarget;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SortedMap;
import java.util.TreeMap;

/**
 * Projections as {@link ModuleMetadata} writes them and {@link ModuleReadback} reads them: one entry
 * per declaration, holding its kind, its module, its name and then each fact's label and value, every
 * part counted the way {@link PublishedRequirements} counts a name.
 *
 * <p>Written in the order of the declarations, so one set of projections is one set of entries.
 */
final class PublishedLinkages {

    private PublishedLinkages() {}

    static List<String> written(Map<LinkageTarget, LinkageRecord> linkages) {
        List<String> out = new ArrayList<>(linkages.size());
        new TreeMap<>(linkages).forEach((target, record) -> {
            StringBuilder entry = new StringBuilder()
                    .append(PublishedRequirements.counted(target.kind()))
                    .append(PublishedRequirements.counted(target.module()))
                    .append(PublishedRequirements.counted(target.name()));
            for (LinkageProjection.Fact fact : record.facts()) {
                entry.append(PublishedRequirements.counted(fact.label()))
                        .append(PublishedRequirements.counted(fact.value()));
            }
            out.add(entry.toString());
        });
        return out;
    }

    /** The projections {@code entries} record, by the declaration — or null where one of them is not
     *  an entry this writes. */
    static SortedMap<LinkageTarget, LinkageRecord> read(List<String> entries) {
        SortedMap<LinkageTarget, LinkageRecord> out = new TreeMap<>();
        for (String entry : entries) {
            int[] at = {0};
            String kind = PublishedRequirements.counted(entry, at);
            String module = kind == null ? null : PublishedRequirements.counted(entry, at);
            String name = module == null ? null : PublishedRequirements.counted(entry, at);
            LinkageTarget target = name == null ? null
                    : LinkageTarget.readingWritten(kind, module, name);
            if (target == null) {
                return null;
            }
            List<LinkageProjection.Fact> facts = new ArrayList<>();
            Set<String> labels = new HashSet<>();
            while (at[0] < entry.length()) {
                String label = PublishedRequirements.counted(entry, at);
                String value = label == null ? null : PublishedRequirements.counted(entry, at);
                if (value == null || !labels.add(label)) {
                    return null;
                }
                facts.add(new LinkageProjection.Fact(label, value));
            }
            if (out.put(target, new LinkageRecord(facts)) != null) {
                return null;
            }
        }
        return out;
    }
}
