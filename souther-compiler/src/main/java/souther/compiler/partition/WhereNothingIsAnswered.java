package souther.compiler.partition;

import souther.compiler.coverage.UnreachableReasons;
import souther.compiler.reading.CoverageRead;
import souther.compiler.reading.NothingAnsweredHere;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

/**
 * The classes at which a body answers nothing: every row sitting there reaches an
 * {@code unreachable}.
 *
 * <p>What a row is owed at is the model's answer and is not changed by this. A class the rules admit
 * stays one a row is owed at however the body describes it, because the body's {@code unreachable}
 * is a statement nothing here proves, and an obligation taken away on its word is the row that
 * would have shown it wrong going unasked for. What this answers is the other question about such
 * an obligation: whether a row that meets it can be written. Every one would reach an
 * {@code unreachable} and be refused (E1911), so an obligation in here is one no row can be told to
 * meet and no build can be told to refuse over — it stays open until the premise is proved or the
 * body answers.
 *
 * <p><b>Every row, and so the union.</b> A part that answers nothing is reached by as many ways as
 * the walk named, and two parts may answer nothing for two values of a third position between
 * them. A row holding an obligation's classes may come any of those ways, so the obligation is in
 * here exactly where the cells of all of them together hold every such row — and asked of one way
 * at a time, a pair two ways share would be a gap no row can close.
 *
 * <p>Whole cells only, and nothing read wider. A way with a condition placed at no class is left out
 * ({@link InteractionCells#whereEach}), which can only leave an obligation outside — never put one
 * in that some row escapes.
 *
 * @param behavior the behavior whose body this is
 * @param regions  one per part that answers nothing, in the order the walk met them
 * @param classes  every class of each position some region narrows, in the order the axis holds
 *                 them: what a position an obligation leaves free may hold. A position no region
 *                 narrows is not here and no region depends on it
 */
public record WhereNothingIsAnswered(String behavior, List<Region> regions,
                                     Map<AxisId, List<String>> classes) {

    /** A body that answers at every row, or one there is no reading of. */
    public static final WhereNothingIsAnswered NONE =
            new WhereNothingIsAnswered("", List.of(), Map.of());

    public WhereNothingIsAnswered {
        Objects.requireNonNull(behavior, "a body is some behavior's");
        regions = List.copyOf(regions);
        Map<AxisId, List<String>> copied = new LinkedHashMap<>();
        classes.forEach((axis, ids) -> copied.put(axis, List.copyOf(ids)));
        classes = Collections.unmodifiableMap(copied);
    }

    /**
     * One part of the body that answers nothing: the cells of every way to it this could place,
     * and the premise it states.
     *
     * @param ways    the classes each way leaves each position it narrows, one map per way. A
     *                position a way says nothing about is not in its map, and a row may hold any
     *                class there
     * @param premise what the part states, and which part it is
     */
    public record Region(List<Map<AxisId, Set<String>>> ways, Premise premise) {

        public Region {
            List<Map<AxisId, Set<String>>> copied = new ArrayList<>();
            for (Map<AxisId, Set<String>> way : ways) {
                Map<AxisId, Set<String>> one = new HashMap<>();
                way.forEach((axis, ids) -> one.put(axis, Set.copyOf(ids)));
                copied.add(Map.copyOf(one));
            }
            ways = List.copyOf(copied);
            Objects.requireNonNull(premise, "a part that answers nothing states something");
        }
    }

    /**
     * What one part of a body states by answering nothing, and which part it is.
     *
     * <p>Told apart by where it stands among the parts of its body and not by its words. Two
     * {@code unreachable}s saying the same thing are two premises, and a premise is one however many
     * obligations rest on it.
     *
     * @param behavior the behavior whose body states it
     * @param part     where it stands among the parts of that body that answer nothing, in the order
     *                 the walk met them
     * @param reasons  what its {@code unreachable}s say, each once, in the order evaluation reaches
     *                 them. The words and not where they are written: no answer about the rows
     *                 holds a place
     */
    public record Premise(String behavior, int part, List<String> reasons) {

        public Premise {
            Objects.requireNonNull(behavior, "a premise is some behavior's body's");
            reasons = List.copyOf(reasons);
            if (part < 0) {
                throw new IllegalArgumentException("a part is somewhere among the parts: " + part);
            }
        }
    }

    /**
     * Where the body {@code behavior} read as {@code read} answers nothing, placed on
     * {@code measured}.
     *
     * <p>Placed the way a cell of the body's decisions is placed ({@link InteractionCells#whereEach}),
     * so a combination of classes this says a run comes to is one those cells would steer a row to.
     */
    public static WhereNothingIsAnswered of(String behavior, CoverageRead.Read read,
                                            MeasuredInput.MeasuredAxes measured) {
        List<Axis> axes = measured.axes();
        List<Region> regions = new ArrayList<>();
        Map<AxisId, List<String>> narrowed = new LinkedHashMap<>();
        List<NothingAnsweredHere> parts = read.answersNothing();
        for (int at = 0; at < parts.size(); at++) {
            NothingAnsweredHere part = parts.get(at);
            List<Map<AxisId, Set<String>>> ways = new ArrayList<>();
            for (InteractionCells.Cell cell : InteractionCells.whereEach(part.ways(), measured)) {
                Map<AxisId, Set<String>> leaves = new HashMap<>();
                for (int axis = 0; axis < axes.size(); axis++) {
                    if (!cell.narrows(axis)) {
                        continue;
                    }
                    Set<String> admitted = new HashSet<>();
                    for (int c = 0; c < axes.get(axis).classes().size(); c++) {
                        if (cell.admits(axis, c)) {
                            admitted.add(axes.get(axis).classes().get(c).id());
                        }
                    }
                    Axis position = axes.get(axis);
                    leaves.put(position.id(), admitted);
                    narrowed.computeIfAbsent(position.id(),
                            _ -> position.classes().stream().map(PartitionClass::id).toList());
                }
                ways.add(leaves);
            }
            regions.add(new Region(ways, new Premise(behavior, at, part.said().stream()
                    .map(UnreachableReasons.Said::reason).distinct().toList())));
        }
        return new WhereNothingIsAnswered(behavior, regions, narrowed);
    }

    /**
     * The premises every row holding {@code fixed} rests on, or nothing where some such row answers.
     *
     * <p>Every row, so the question is whether the classes {@code fixed} leaves — one at each
     * position it names, any at every other — are inside the cells of every region together. The
     * premises named are the parts such a row may reach, which is every region one of whose cells
     * meets them: which of them a run aborts at is which way it came.
     */
    public List<Premise> everyRowAt(Set<ClassOfAPosition> fixed) {
        if (regions.isEmpty()) {
            return List.of();
        }
        Map<AxisId, Set<String>> box = new LinkedHashMap<>();
        classes.forEach((axis, ids) -> box.put(axis, new LinkedHashSet<>(ids)));
        for (ClassOfAPosition each : fixed) {
            if (box.containsKey(each.at())) {
                box.put(each.at(), new LinkedHashSet<>(Set.of(each.classId())));
            }
        }
        List<Map<AxisId, Set<String>>> cells = new ArrayList<>();
        Set<Premise> resting = new LinkedHashSet<>();
        for (Region region : regions) {
            for (Map<AxisId, Set<String>> way : region.ways()) {
                if (meets(way, box)) {
                    cells.add(way);
                    resting.add(region.premise());
                }
            }
        }
        return covered(box, cells) ? List.copyOf(resting) : List.of();
    }

    /**
     * Whether every row in {@code box} is in one of {@code cells}.
     *
     * <p>Split where the cells first part company, and only there. Classes of one position that
     * every cell meeting the box admits alike are one case for all of them, so they stay together;
     * a position no cell narrows within the box needs no split at all. Each split leaves the box
     * smaller at one position, so this ends, and how far it goes is how many ways the cells
     * actually tell the box apart.
     */
    private static boolean covered(Map<AxisId, Set<String>> box,
                                   List<Map<AxisId, Set<String>>> cells) {
        List<Map<AxisId, Set<String>>> meeting = new ArrayList<>();
        for (Map<AxisId, Set<String>> cell : cells) {
            if (meets(cell, box)) {
                if (holds(cell, box)) {
                    return true;
                }
                meeting.add(cell);
            }
        }
        if (meeting.isEmpty()) {
            return false;
        }
        for (Map.Entry<AxisId, Set<String>> position : box.entrySet()) {
            Map<List<Boolean>, Set<String>> alike = new LinkedHashMap<>();
            for (String id : position.getValue()) {
                List<Boolean> admittedBy = new ArrayList<>();
                for (Map<AxisId, Set<String>> cell : meeting) {
                    Set<String> leaves = cell.get(position.getKey());
                    admittedBy.add(leaves == null || leaves.contains(id));
                }
                alike.computeIfAbsent(admittedBy, _ -> new LinkedHashSet<>()).add(id);
            }
            if (alike.size() < 2) {
                continue;
            }
            for (Set<String> group : alike.values()) {
                Map<AxisId, Set<String>> part = new LinkedHashMap<>(box);
                part.put(position.getKey(), group);
                if (!covered(part, meeting)) {
                    return false;
                }
            }
            return true;
        }
        // Every cell meets the box and none holds it, and no position tells them apart within it:
        // each of them leaves out the same rows, which is rows none of them holds.
        return false;
    }

    /** Whether some row in {@code box} is in {@code cell}. */
    private static boolean meets(Map<AxisId, Set<String>> cell, Map<AxisId, Set<String>> box) {
        for (Map.Entry<AxisId, Set<String>> each : cell.entrySet()) {
            Set<String> held = box.get(each.getKey());
            if (held != null && held.stream().noneMatch(each.getValue()::contains)) {
                return false;
            }
        }
        return true;
    }

    /** Whether every row in {@code box} is in {@code cell}. */
    private static boolean holds(Map<AxisId, Set<String>> cell, Map<AxisId, Set<String>> box) {
        for (Map.Entry<AxisId, Set<String>> each : cell.entrySet()) {
            Set<String> held = box.get(each.getKey());
            if (held == null || !each.getValue().containsAll(held)) {
                return false;
            }
        }
        return true;
    }
}
