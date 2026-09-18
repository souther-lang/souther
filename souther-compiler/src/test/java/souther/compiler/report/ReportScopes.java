package souther.compiler.report;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * Every report a reader can be handed, which is what a law about reports is held over.
 *
 * <p>Read off {@link AdequacyReport#only(String, String)} and not off the way a report nests. Both
 * of its arguments are named or not, independently, so there are four of these — and a population
 * walked as modules and then their behaviors produces three of them. The one it leaves out is a
 * behavior named without a module, which a run allows and which is its own report: a name two
 * modules both declare gathers into one there and into neither of the others.
 *
 * <p>In one place because two laws are held over these. Enumerated where each is asked, the two
 * populations drift, and a projection added later is remembered for one of them.
 *
 * @param name what to call this one when a law fails on it
 * @param report the report itself
 */
record ReportScopes(String name, AdequacyReport report) {

    /** Every scope this report can be narrowed to, itself among them. */
    static List<ReportScopes> of(String name, AdequacyReport whole) {
        List<ReportScopes> out = new ArrayList<>();
        out.add(new ReportScopes(name, whole));
        Set<String> behaviors = new LinkedHashSet<>();
        for (AdequacyReport.ModuleReport module : whole.modules()) {
            out.add(new ReportScopes(module.module(), whole.only(module.module(), null)));
            for (AdequacyReport.BehaviorReport behavior : module.behaviors()) {
                behaviors.add(behavior.name());
                out.add(new ReportScopes(module.module() + "/" + behavior.name(),
                        whole.only(module.module(), behavior.name())));
            }
        }
        // A name and no module, which gathers whatever declares that name. Asked once per name
        // rather than once per declaration of it: the report is the same either way, and the
        // second asking would say a name two modules share is two scopes.
        for (String behavior : behaviors) {
            out.add(new ReportScopes("*/" + behavior, whole.only(null, behavior)));
        }
        return List.copyOf(out);
    }
}
