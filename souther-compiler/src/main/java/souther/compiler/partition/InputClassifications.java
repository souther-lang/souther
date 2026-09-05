package souther.compiler.partition;

import souther.compiler.inputs.Membership;
import souther.compiler.observe.Classification;
import souther.compiler.observe.Incompleteness;
import souther.compiler.observe.ObservedValue;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * Which class each of a behavior's inputs fell in.
 *
 * <p>Values, not class names, so where they fall has to be read back out of them. The values are
 * already the compiler's own ({@link ObservedValue}), so this is a walk down a path and a question
 * put to each class.
 *
 * <p><b>A tuple of values and never a row.</b> A written {@code example} row has one; so does a
 * value in scope that a generated row is composed against, and so does a candidate the generator
 * has just built. All three are placed by this and by nothing else — a second placement written for
 * one of them would be a second answer to where a value falls, and the two would agree until one
 * moved. Whatever a caller has a tuple of values for, it hands that over ({@code row.inputs()} for
 * a row) and gets back the same map every other caller gets.
 *
 * <p>A value that could not be read leaves <em>that axis</em> unclassified and nothing else. One
 * enormous string still says which case the values beside it were, and a measure that gave up on
 * the whole tuple because of an unrelated field would report gaps that were already filled.
 */
public final class InputClassifications {

    /**
     * Where each axis's value fell, for the axes that have classes. An axis the model only bounds
     * has nothing to fall into and is left out.
     *
     * <p>Takes the classes with the input they were measured at, and not a walk beside a list of
     * them. Which position a value is written at is the walk's answer and which class it falls in
     * is the axis's, and the two are only about one row where both came from one reading — two
     * behaviors taking a parameter spelled the same way have an axis apiece at the same path, and
     * placed through the wrong walk a row lands in classes nothing measured where it was read.
     */
    public static Map<AxisId, Classification> of(List<ObservedValue> inputs,
                                                 MeasuredInput.MeasuredAxes axes) {
        List<Classification> placed = placedAt(inputs, axes);
        Map<AxisId, Classification> out = new LinkedHashMap<>();
        for (int at = 0; at < axes.size(); at++) {
            if (placed.get(at) != null) {
                out.put(axes.get(at).id(), placed.get(at));
            }
        }
        return Map.copyOf(out);
    }

    /**
     * The same, in the order the axes were handed over.
     *
     * <p>What a reader walking the measurement wants: it asked for these axes in this order, so
     * what comes back is at the place it asked. Keyed by the axis instead, such a reader looks its
     * own axis up in the answer it was just given — which is the shape that reads a measure of
     * another measurement as a class no row reached.
     *
     * <p>Null at an axis the model only bounds. There is nothing there for a value to fall into,
     * and a reader walking the run of axes is told so at the place the axis stands rather than by
     * an entry that is not there.
     */
    public static List<Classification> placedAt(List<ObservedValue> inputs,
                                                MeasuredInput.MeasuredAxes axes) {
        BehaviorInputs where = axes.subject().inputs();
        List<Classification> out = new ArrayList<>(axes.size());
        for (Axis axis : axes.axes()) {
            out.add(axis.derivable() ? classify(inputs, where, axis) : null);
        }
        return java.util.Collections.unmodifiableList(out);
    }



    /**
     * Which class the value at {@code axis} fell in, or why none of them could say.
     *
     * <p>The classes answer for themselves, including about a value none of them could read. This
     * used to test the value's shape here first, which is the same question asked in a second place
     * and answered from a different node: a classifier may read through the value — a number at a
     * position is the number inside the newtype named there — so a limit reached one level in left
     * a construction this saw nothing wrong with, and the reason came out as the one the last line
     * had to guess.
     */
    private static Classification classify(List<ObservedValue> inputs, BehaviorInputs where,
                                           Axis axis) {
        if (!(where.occurrencesAt(inputs, axis.path())
                instanceof WalkResult.Reached(List<BehaviorInputs.Occurrence> values))) {
            return Classification.unreadable(Incompleteness.Code.VALUE_UNREADABLE,
                    axis.id().behavior(), axis.id().term());
        }
        // Every value here, the class it is in, and the element it came from. One value at most
        // positions; as many as were written at a position inside a sequence, where they need not
        // fall together — and where one of them being unreadable leaves the classes the others
        // reached standing, since each is a value of its own.
        List<Classification.At> in = new ArrayList<>();
        Incompleteness stopped = null;
        for (BehaviorInputs.Occurrence value : values) {
            switch (classifyOne(axis, value.value())) {
                case Classification.Classified found -> found.classIds().forEach(id ->
                        in.add(new Classification.At(value.at(), id)));
                case Classification.Unclassified why -> {
                    if (stopped == null) {
                        stopped = why.reason();
                    }
                }
            }
        }
        // Both, and not one instead of the other. A value one class holds and a value beside it
        // nothing could read are two facts about one tuple: the classes it covers stand, and the
        // measurement here is short of what the rest of the list says. Kept apart, either the
        // coverage is thrown away or the measure calls itself complete over a value nothing looked
        // at. No element written at all is neither — it was read, and is in no class.
        return Classification.at(in, stopped);
    }

    /** Where one value at the position falls, or why no class could say. */
    private static Classification classifyOne(Axis axis, ObservedValue value) {
        List<String> ids = new ArrayList<>();
        List<Membership> answers = new ArrayList<>();
        for (PartitionClass each : axis.classes()) {
            ids.add(each.id());
            answers.add(Recognitions.membershipOf(each.recognises(), value));
        }
        return decided(axis.id(), ids, answers, value);
    }

    /**
     * Where a value falls, given what each class of one axis made of it.
     *
     * <p>Every class answers before anything is decided. A class may read less of a value than the
     * one after it, so one saying it could not read says nothing about the rest — including that the
     * rest cannot hold it. An incompleteness is what is left once no class has claimed the value.
     *
     * <p>Its own function, taking the answers rather than the classes that gave them, because what
     * is written here is a rule about answers and the three ways it can be broken are not states any
     * class can now be built in: what a class recognises is a {@link Recognition}, every one of them
     * reads a value the same way, and so the contract below is held to by something no producer in
     * this compiler can reach. A rule nothing can exercise is a rule nobody can check.
     *
     * @param ids     what each class is called, in the order they were asked
     * @param answers what each of them made of the value, in the same order
     * @param about   the value they were asked about, for the sentence a broken contract prints, and
     *                for nothing else. Null where a caller has none to name
     */
    static Classification decided(AxisId at, List<String> ids, List<Membership> answers,
                                  ObservedValue about) {
        if (ids.size() != answers.size()) {
            throw new IllegalArgumentException(
                    "one answer per class: " + ids.size() + " classes, " + answers.size());
        }
        Incompleteness.Code incomplete = null;
        boolean disagreed = false;
        for (int i = 0; i < answers.size(); i++) {
            switch (answers.get(i)) {
                case Membership.Match _ -> {
                    // A class that holds the value settles it, whatever the ones beside it could not
                    // read and whatever they disagreed about. What the value is in is an answer; why
                    // something else could not read it is what is left when there is no answer.
                    return Classification.in(ids.get(i));
                }
                case Membership.Incomplete why -> {
                    if (incomplete == null) {
                        incomplete = why.code();
                    } else if (incomplete != why.code()) {
                        disagreed = true;
                    }
                }
                case Membership.NoMatch _ -> { }
            }
        }
        // Two readings of one value that disagree about whether it is there. Held to rather than
        // picked between: today every class of a numeric position reads through the same reader,
        // so nothing produces one.
        if (disagreed) {
            throw new IllegalStateException("classes of " + at
                    + " disagree about why the value could not be read");
        }
        if (incomplete != null) {
            return Classification.unreadable(incomplete, at.behavior(), at.term());
        }
        // Every class read the value and none holds it, which `Axis` says cannot happen: its classes
        // are exhaustive over the position's values. So this is that contract broken rather than
        // anything about the value, and saying it could not be read would be reporting a
        // measurement failure for a defect in the partition.
        throw new IllegalStateException("no class of " + at + " holds a value it read: " + about);
    }

    private InputClassifications() {}
}
