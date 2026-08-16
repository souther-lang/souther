package souther.compiler.check;

import souther.compiler.types.TypeSymbol;

import java.util.HashMap;
import java.util.Map;

/**
 * What is known of every declaration while the counts are being worked out.
 *
 * <p>Two states and not one. A declaration the rising has not finished with is at the bottom:
 * nothing has been shown of it, which is where a rising starts and is not the same as having been
 * shown to have no value. Keeping them apart is what stops a proof being written out of an
 * assumption — with one state for both, {@code A} would carry "no value, because {@code B} has none"
 * while {@code B} carried the same about {@code A}, and neither would have been shown anything.
 *
 * <p>What a reading takes from either is the same, which is why the two can live in one place. A
 * declaration reached by name is read for its count alone and its proof is left where it is, so a
 * name at the bottom and a name shown to have none both answer {@link Emptiness.TheNameHasNone} —
 * true of the second already, and of the first once the rising has stopped with it still there.
 * {@link TypeCardinality} is where that is made good.
 *
 * <p>Nothing is written in here but through the two states. A caller with a count to record says so,
 * and a caller starting a rising says that, and there is no third thing to put in.
 */
final class Answers {

    /** What the rising has arrived at for one declaration. */
    private sealed interface Answer {

        /** Nothing has been shown of it yet. */
        record AtBottom() implements Answer {}

        /** What it comes to. */
        record Settled(Cardinality count) implements Answer {}
    }

    private static final Answer AT_BOTTOM = new Answer.AtBottom();

    private final Map<TypeSymbol, Answer> by;

    private Answers(Map<TypeSymbol, Answer> by) {
        this.by = by;
    }

    /** Nothing known of anything. */
    static Answers empty() {
        return new Answers(new HashMap<>());
    }

    /** The counts already worked out, with nothing standing at the bottom. */
    static Answers settled(Map<TypeSymbol, Cardinality> counts) {
        Answers answers = empty();
        counts.forEach(answers::settle);
        return answers;
    }

    /** What {@code name} comes to. */
    void settle(TypeSymbol name, Cardinality count) {
        by.put(name, new Answer.Settled(count));
    }

    /** Nothing shown of {@code name} yet, which is where a rising starts it. */
    void atBottom(TypeSymbol name) {
        by.put(name, AT_BOTTOM);
    }

    /** What {@code name} was settled at, or null while nothing has been shown of it. */
    Cardinality settledAt(TypeSymbol name) {
        return by.get(name) instanceof Answer.Settled settled ? settled.count() : null;
    }

    /**
     * How many values {@code name} has, as a reading that reached it by name may take it.
     *
     * <p>Nothing is known of a name this never reached, which is the answer that refuses nothing. A
     * name with no value answers with the proof that stops at the name, whichever of the two states
     * it is in: what is beyond the name is that declaration's own answer and is not carried here.
     */
    Cardinality of(TypeSymbol name) {
        return switch (by.get(name)) {
            case null -> Cardinality.UNKNOWN;
            case Answer.AtBottom _ -> Cardinality.none(new Emptiness.TheNameHasNone(name));
            case Answer.Settled settled -> settled.count() instanceof Cardinality.None
                    ? Cardinality.none(new Emptiness.TheNameHasNone(name))
                    : settled.count();
        };
    }

    /**
     * Every count settled, which every name reached has to be by the time the reading is over.
     *
     * <p>A name left at the bottom is nothing having been shown of it, and answering with the
     * absence of it would put a type nothing can build back among the ones that can.
     */
    Map<TypeSymbol, Cardinality> everySettled() {
        Map<TypeSymbol, Cardinality> counts = new HashMap<>();
        by.forEach((name, answer) -> {
            if (!(answer instanceof Answer.Settled settled)) {
                throw new IllegalStateException(
                        "the rising left nothing shown of `" + name + "`, which is not an answer");
            }
            counts.put(name, settled.count());
        });
        return counts;
    }
}
