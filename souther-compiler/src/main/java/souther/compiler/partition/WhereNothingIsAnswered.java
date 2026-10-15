package souther.compiler.partition;

import souther.compiler.coverage.UnreachableReasons;
import souther.compiler.reading.CoverageRead;
import souther.compiler.reading.NothingAnsweredHere;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

/**
 * The rows at which a body answers nothing: every row sitting there reaches an
 * {@code unreachable}.
 *
 * <p>What a row is owed at is the model's answer and is not changed by this. An obligation stays one
 * a row is owed at however the body describes it, because the body's {@code unreachable} is a
 * statement nothing here proves, and an obligation taken away on its word is the row that would have
 * shown it wrong going unasked for. What this answers is the other question about such an
 * obligation: whether a row that meets it can be written. Every one would reach an
 * {@code unreachable} and be refused (E1911), so an obligation in here is one no row can be told to
 * meet and no build can be told to refuse over — it stays open until the premise is proved or the
 * body answers.
 *
 * <p><b>Every row, and so the union.</b> A part that answers nothing is reached by as many ways as
 * the walk named, and two parts may answer nothing for two values of a third position between
 * them. A row an obligation asks for may come any of those ways, so the obligation is in here
 * exactly where the cells of all of them together hold every such row — and asked of one way at a
 * time, an obligation two ways share would be a gap no row can close.
 *
 * <p>Drawn narrow, and asked of a region drawn wide. A way with a condition placed at no class is
 * left out ({@link InteractionCells#whereEach}), and what an obligation asks for keeps every row a
 * condition could not place ({@link InteractionCells#holdingEvery}). So the one can be inside the
 * other only where the rows themselves are; what is lost is an obligation left outside, never one
 * put in that some row escapes.
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
     * One part of the body that answers nothing: the rows of every way to it this could place, and
     * the premise it states.
     *
     * @param where   the rows that come to the part, drawn narrow: a row in here is one that does
     * @param premise what the part states, and which part it is
     */
    public record Region(RowRegion where, Premise premise) {

        public Region {
            Objects.requireNonNull(where, "a part is come to by some rows or none");
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
        Set<AxisId> narrowed = new LinkedHashSet<>();
        List<NothingAnsweredHere> parts = read.answersNothing();
        for (int at = 0; at < parts.size(); at++) {
            NothingAnsweredHere part = parts.get(at);
            List<RowRegion.Cell> ways = new ArrayList<>();
            for (InteractionCells.Cell cell : InteractionCells.whereEach(part.ways(), measured)) {
                RowRegion.Cell placed = RowRegion.Cell.of(cell, axes);
                narrowed.addAll(placed.classes().keySet());
                ways.add(placed);
            }
            regions.add(new Region(RowRegion.of(ways), new Premise(behavior, at, part.said()
                    .stream().map(UnreachableReasons.Said::reason).distinct().toList())));
        }
        Map<AxisId, List<String>> classes = new LinkedHashMap<>();
        for (Axis axis : axes) {
            if (narrowed.contains(axis.id())) {
                classes.put(axis.id(), axis.classes().stream().map(PartitionClass::id).toList());
            }
        }
        return new WhereNothingIsAnswered(behavior, regions, classes);
    }

    /**
     * The premises every row of {@code obligation} rests on, or nothing where some such row answers.
     *
     * <p>Every row, so the question is whether each cell of the obligation — one class at each
     * position it narrows, any at every other — is inside the cells of every region together. The
     * premises named are the parts such a row may reach, which is every region one of whose cells
     * meets one of the obligation's: which of them a run aborts at is which way it came.
     *
     * <p>Nothing for an obligation no row is in. Whether a row can be written there is a question
     * about the obligation and not about where the body answers, and every row of none reaching an
     * {@code unreachable} is not a premise anything rests on.
     */
    public List<Premise> everyRowIn(RowRegion obligation) {
        if (regions.isEmpty()) {
            return List.of();
        }
        BitSet resting = new BitSet();
        for (RowRegion.Cell cell : cellsOf(obligation)) {
            Map<AxisId, Set<String>> box = boxOf(cell);
            if (box == null) {
                continue;
            }
            List<Map<AxisId, Set<String>>> meeting = new ArrayList<>();
            for (int at = 0; at < regions.size(); at++) {
                for (RowRegion.Cell way : cellsOf(regions.get(at).where())) {
                    if (meets(way.classes(), box)) {
                        meeting.add(way.classes());
                        resting.set(at);
                    }
                }
            }
            if (!covered(box, meeting)) {
                return List.of();
            }
        }
        List<Premise> out = new ArrayList<>();
        resting.stream().forEach(at -> out.add(regions.get(at).premise()));
        return List.copyOf(out);
    }

    /**
     * The premises every row holding {@code fixed} rests on, or nothing where some such row answers:
     * the rows a class of one position, or a combination of classes of several, asks for.
     */
    public List<Premise> everyRowAt(Set<ClassOfAPosition> fixed) {
        Map<AxisId, Set<String>> at = new HashMap<>();
        for (ClassOfAPosition each : fixed) {
            at.computeIfAbsent(each.at(), _ -> new LinkedHashSet<>()).add(each.classId());
        }
        return everyRowIn(RowRegion.of(List.of(new RowRegion.Cell(at))));
    }

    /** The cells {@code rows} is the union of: none for no row, and one naming nothing for all. */
    private static List<RowRegion.Cell> cellsOf(RowRegion rows) {
        return switch (rows) {
            case RowRegion.None _ -> List.of();
            case RowRegion.All _ -> List.of(new RowRegion.Cell(Map.of()));
            case RowRegion.Cells(var cells) -> cells;
        };
    }

    /**
     * The classes {@code cell} leaves each position some region narrows, or null where it leaves one
     * of them none. A position no region narrows is left out: every region holds all of it alike.
     */
    private Map<AxisId, Set<String>> boxOf(RowRegion.Cell cell) {
        Map<AxisId, Set<String>> box = new LinkedHashMap<>();
        for (Map.Entry<AxisId, List<String>> each : classes.entrySet()) {
            Set<String> left = new LinkedHashSet<>(each.getValue());
            Set<String> asked = cell.classes().get(each.getKey());
            if (asked != null) {
                left.retainAll(asked);
            }
            if (left.isEmpty()) {
                return null;
            }
            box.put(each.getKey(), left);
        }
        return box;
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
