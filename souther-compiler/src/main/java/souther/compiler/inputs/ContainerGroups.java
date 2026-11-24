package souther.compiler.inputs;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The containers a question is asked of each way, kept in groups, and which group each number of
 * the question is in.
 *
 * <p>Two things are said of a container and they are two. A container <em>relates</em> the numbers
 * that walk it: what is said of the numbers of one container, an identity among them that is put on
 * when they are asked of as much as a rule, holds of them together, so they are in one group
 * whether or not what the container holds is already settled. A container is <em>asked of</em>
 * only where nothing settles it, which is the only place it has two ways to be held; a settled one
 * is no case to look at, and still a reason two numbers are one question.
 *
 * <p>A number is in the group of the part of the rules that weighs it, and the groups of the parts
 * whose numbers walk one container are one group. A number no rule weighs is in a group of its own.
 * What the rules leave a number is what the part of them that weighs it leaves, so the question over
 * a form is the sum of the questions over the pieces of it that are in one group each, and an
 * emptiness is shown by any group.
 *
 * <p>Plain data and no reading of any input: the caller says, of each number, which part weighs it
 * and which container it walks, and what is said here is only which of them are one.
 */
final class ContainerGroups {

    /**
     * Containers asked of together, and whether the question names a number of them.
     *
     * @param containers the containers asked of, in the order they were said
     * @param reached    whether a number the question is about is weighed by a part of this group,
     *                   or walks one of its containers
     */
    record Group(List<TermPath> containers, boolean reached) {}

    private final Map<Object, Object> joined = new HashMap<>();
    private final Map<Object, Object> partOf = new HashMap<>();
    private final Set<TermPath> asked = new LinkedHashSet<>();
    private final Set<Object> askedKeys = new HashSet<>();

    /**
     * Says of one number which part of the rules weighs it, which container it walks, whether that
     * container is one to ask of each way, and whether the question is about the number.
     *
     * @param number     what the number is called by whoever asks
     * @param part       what the part weighing it is called by, or null where it stands nowhere
     * @param container  the container it walks, or null where it walks none
     * @param settled    whether what the container holds is already settled, so that it relates
     *                   numbers and is not asked of each way
     * @param ofTheQuestion whether the question is about the number
     */
    void say(Object number, Object part, TermPath container, boolean settled,
             boolean ofTheQuestion) {
        if (part != null) {
            partOf.put(number, part);
            if (ofTheQuestion) {
                askedKeys.add(part);
            }
        }
        if (container == null) {
            return;
        }
        if (part != null) {
            join(container, part);
        }
        if (ofTheQuestion) {
            askedKeys.add(container);
        }
        if (!settled) {
            asked.add(container);
        }
    }

    /** What the group of {@code number} is called by: the number itself where nothing weighs it. */
    Object keyOf(Object number) {
        Object part = partOf.get(number);
        return part == null ? number : rootOf(part);
    }

    /** The containers asked of in the group called {@code key}, in the order they were said. */
    List<TermPath> containersOf(Object key) {
        List<TermPath> out = new ArrayList<>();
        for (TermPath container : asked) {
            if (rootOf(container).equals(key)) {
                out.add(container);
            }
        }
        return out;
    }

    /** The groups that have a container to ask of. */
    List<Group> groups() {
        Map<Object, List<TermPath>> held = new LinkedHashMap<>();
        for (TermPath container : asked) {
            held.computeIfAbsent(rootOf(container), _ -> new ArrayList<>()).add(container);
        }
        Set<Object> reached = new HashSet<>();
        for (Object key : askedKeys) {
            reached.add(rootOf(key));
        }
        List<Group> out = new ArrayList<>();
        held.forEach((root, containers) -> out.add(
                new Group(List.copyOf(containers), reached.contains(root))));
        return out;
    }

    private void join(Object a, Object b) {
        Object first = rootOf(a);
        Object second = rootOf(b);
        if (!first.equals(second)) {
            joined.put(second, first);
        }
    }

    private Object rootOf(Object key) {
        Object at = key;
        while (joined.containsKey(at)) {
            at = joined.get(at);
        }
        return at;
    }
}
