package souther.test;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.function.Predicate;

/**
 * The names this repository keeps for a row.
 *
 * <p>One row is one line of an {@code example} or {@code fake} table. The things holding rows nest,
 * and every level of them can be spelled {@code rows} without a reader being told which they have —
 * a count taken off the wrong one is a count of groups that reads as a count of rows.
 *
 * <p>The spelling is here because it is the same in every module. What a row <em>is</em>, and what
 * may hold one, is not: only the compiler declares a row type, so only its own check has an
 * admitting side to state. Every other module has none, and says so by letting nothing take the
 * name at all.
 */
public final class TheBareRowNames {

    private TheBareRowNames() {
    }

    /** What a member may not be called unless it answers a row. */
    public static final Set<String> MEMBERS = Set.of("row", "rows");

    /** What a type may not be called unless it is one. */
    public static final Set<String> TYPES = Set.of("Row", "Rows");

    /**
     * The declarations of {@code module} that take one of {@link #MEMBERS}, less those excused.
     *
     * @param excused what the rule does not reach here, which is a module's own to say
     */
    public static List<String> takenIn(WhatAModuleDeclares module,
                                       Predicate<WhatAModuleDeclares.Declared> excused) {
        List<String> found = new ArrayList<>();
        for (WhatAModuleDeclares.Declared each : module.taking(MEMBERS)) {
            if (!excused.test(each)) {
                found.add(each.shown());
            }
        }
        return found;
    }

    /** The types of {@code module} called {@code Row} or {@code Rows}. */
    public static List<String> typesIn(WhatAModuleDeclares module) {
        List<String> found = new ArrayList<>();
        for (var each : module.classes()) {
            String internal = each.thisClass().asInternalName();
            String last = internal.substring(internal.lastIndexOf('/') + 1);
            if (TYPES.contains(last.substring(last.lastIndexOf('$') + 1))) {
                found.add(internal);
            }
        }
        return found;
    }
}
