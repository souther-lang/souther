package souther.compiler.execute;

import souther.compiler.diag.SourcePos;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * The values a module declares that are to be built, in the order they are built.
 *
 * <p>A value takes nothing of a caller and is built once, where its module builds it, so what is
 * asked is the module, each value, and which of the others its build is handed. A value that reads
 * another is built from that other, which the region that builds it has built already and hands
 * over. Each value is one step and appears once, after every value it is handed: a value several
 * others read is built once and handed to each, which is what the module does.
 *
 * @param writtenIn the module the values are declared in, which is the compile whose classes they
 *                  are built from
 * @param inOrder   the values, each after the ones it is handed
 */
public record ValueBuild(String writtenIn, List<Step> inOrder) {

    /**
     * One value to build.
     *
     * @param name   the value, as the module declares it
     * @param pos    where the module declares it
     * @param handed the values this one is handed, in the order it is handed them, each a step
     *               before this one
     */
    public record Step(String name, SourcePos pos, List<String> handed) {

        public Step {
            if (name == null || name.isEmpty() || pos == null) {
                throw new IllegalArgumentException("a value to build has a name and a place: "
                        + name);
            }
            handed = List.copyOf(handed);
        }
    }

    public ValueBuild {
        if (writtenIn == null || writtenIn.isEmpty()) {
            throw new IllegalArgumentException("values are some module's: " + writtenIn);
        }
        inOrder = List.copyOf(inOrder);
        Set<String> before = new HashSet<>();
        for (Step each : inOrder) {
            if (!before.containsAll(each.handed()) || !before.add(each.name())) {
                throw new IllegalArgumentException("`" + each.name() + "` is built once, after"
                        + " the values it is handed: " + each.handed());
            }
        }
    }
}
