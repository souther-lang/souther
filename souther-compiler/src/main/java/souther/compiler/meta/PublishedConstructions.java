package souther.compiler.meta;

import souther.compiler.codegen.ConstructionLink;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;

/**
 * The constructors a module's classes link against in other modules, as {@link ModuleMetadata}
 * writes them and {@link ModuleReadback} reads them: one entry per behavior built, holding the
 * declaring module, the behavior, the constructor's descriptor, and the module and name of each
 * dependency handed to it in order — every part counted the way {@link PublishedRequirements}
 * counts a name.
 */
final class PublishedConstructions {

    private PublishedConstructions() {}

    static List<String> written(List<ConstructionLink> links) {
        List<String> out = new ArrayList<>(links.size());
        for (ConstructionLink link : links) {
            StringBuilder entry = new StringBuilder()
                    .append(PublishedRequirements.counted(link.target().module()))
                    .append(PublishedRequirements.counted(link.target().name()))
                    .append(PublishedRequirements.counted(link.constructor()));
            for (ValueName.Behavior dependency : link.dependencies()) {
                entry.append(PublishedRequirements.counted(dependency.module()))
                        .append(PublishedRequirements.counted(dependency.name()));
            }
            out.add(entry.toString());
        }
        return out;
    }

    /** The links {@code entries} name, or null where one of them is not an entry this writes. */
    static List<ConstructionLink> read(List<String> entries) {
        List<ConstructionLink> out = new ArrayList<>(entries.size());
        for (String entry : entries) {
            int[] at = {0};
            String module = PublishedRequirements.counted(entry, at);
            String name = module == null ? null : PublishedRequirements.counted(entry, at);
            String constructor = name == null ? null : PublishedRequirements.counted(entry, at);
            if (constructor == null) {
                return null;
            }
            List<ValueName.Behavior> dependencies = new ArrayList<>();
            while (at[0] < entry.length()) {
                String from = PublishedRequirements.counted(entry, at);
                String named = from == null ? null : PublishedRequirements.counted(entry, at);
                if (named == null) {
                    return null;
                }
                dependencies.add(new ValueName.Behavior(from, named));
            }
            out.add(new ConstructionLink(new ValueName.Behavior(module, name), dependencies,
                    constructor));
        }
        return List.copyOf(out);
    }
}
