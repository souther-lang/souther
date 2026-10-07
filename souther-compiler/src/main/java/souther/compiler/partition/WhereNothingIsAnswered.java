package souther.compiler.partition;

import souther.compiler.coverage.UnreachableReasons;
import souther.compiler.reading.CoverageRead;
import souther.compiler.reading.NothingAnsweredHere;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * The classes at which a body answers nothing: every row sitting there reaches an
 * {@code unreachable}.
 *
 * <p>What a row is owed at is the model's answer and is not changed by this. A class the rules admit
 * stays one a row is owed at however the body describes it, because the body's {@code unreachable}
 * is a statement nothing here proves, and an obligation taken away on its word is the row that
 * would have shown it wrong going unasked for. What this answers is the other question about such
 * an obligation: whether a row that meets it can be written. Every one would reach the
 * {@code unreachable} and be refused (E1911), so an obligation in here is one no row can be told to
 * meet and no build can be told to refuse over — it stays open until the premise is proved or the
 * body answers.
 *
 * <p>Whole cells only. A part of a body is reached by the ways the walk over it names, and a cell is
 * in here only where every row with those classes comes one of those ways — so a part reached where
 * a third position is one way says nothing about the pair of the other two, which a row can still
 * meet by holding the third the other way.
 *
 * @param parts one per way to a part that answers nothing which places at classes, in the order the
 *              walk met them
 */
public record WhereNothingIsAnswered(List<Part> parts) {

    /** A body that answers at every row, or one there is no reading of. */
    public static final WhereNothingIsAnswered NONE = new WhereNothingIsAnswered(List.of());

    public WhereNothingIsAnswered {
        parts = List.copyOf(parts);
    }

    /**
     * One way to a part that answers nothing, as the classes it leaves each position it names.
     *
     * <p>Held by the axis and the class, which is how an obligation names what it is at. A position
     * the way says nothing about is not here, and a row may hold any class there.
     *
     * @param leaves  the classes the way leaves each position it narrows. Looked up and never
     *                walked, so what order it would iterate in is no part of the answer
     * @param reasons what the {@code unreachable}s a run there aborts at say, each once. The words
     *                and not where they are written, which no answer about the rows holds
     */
    public record Part(Map<AxisId, Set<String>> leaves, List<String> reasons) {

        public Part {
            Map<AxisId, Set<String>> copied = new HashMap<>();
            leaves.forEach((axis, classes) -> copied.put(axis, Set.copyOf(classes)));
            leaves = Map.copyOf(copied);
            reasons = List.copyOf(reasons);
        }

        /** Whether every row holding {@code fixed} and anything at all elsewhere comes here. */
        boolean holdsEveryRowAt(Set<ClassOfAPosition> fixed) {
            for (Map.Entry<AxisId, Set<String>> each : leaves.entrySet()) {
                if (fixed.stream().noneMatch(at -> at.at().equals(each.getKey())
                        && each.getValue().contains(at.classId()))) {
                    return false;
                }
            }
            return true;
        }
    }

    /**
     * Where the body read as {@code read} answers nothing, placed on {@code axes}.
     *
     * <p>Placed the way a cell of the body's decisions is placed ({@link InteractionCells#whereEach}),
     * so a combination of classes this says a run comes to is one those cells would steer a row to.
     */
    public static WhereNothingIsAnswered of(CoverageRead.Read read, List<Axis> axes) {
        List<Part> out = new ArrayList<>();
        for (NothingAnsweredHere part : read.answersNothing()) {
            for (InteractionCells.Cell cell : InteractionCells.whereEach(part.ways(), axes)) {
                Map<AxisId, Set<String>> leaves = new HashMap<>();
                for (int axis = 0; axis < axes.size(); axis++) {
                    if (!cell.narrows(axis)) {
                        continue;
                    }
                    Set<String> classes = new HashSet<>();
                    for (int c = 0; c < axes.get(axis).classes().size(); c++) {
                        if (cell.admits(axis, c)) {
                            classes.add(axes.get(axis).classes().get(c).id());
                        }
                    }
                    leaves.put(axes.get(axis).id(), classes);
                }
                out.add(new Part(leaves, part.said().stream()
                        .map(UnreachableReasons.Said::reason).distinct().toList()));
            }
        }
        return new WhereNothingIsAnswered(out);
    }

    /**
     * The part every row holding {@code fixed} comes to, or empty where some such row answers.
     *
     * <p>The first the walk met, where more than one does. Which of them a row aborts at is which way
     * it came, and a row sitting at these classes and nowhere else in particular may come any of
     * them; the reasons of the first are the ones a reader is shown.
     */
    public Optional<Part> holdingEveryRowAt(Set<ClassOfAPosition> fixed) {
        for (Part each : parts) {
            if (each.holdsEveryRowAt(fixed)) {
                return Optional.of(each);
            }
        }
        return Optional.empty();
    }
}
