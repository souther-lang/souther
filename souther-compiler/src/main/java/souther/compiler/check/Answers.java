package souther.compiler.check;

import souther.compiler.types.TypeSymbol;

import java.util.HashMap;
import java.util.Map;
import java.util.function.Supplier;

/**
 * What is known of every declaration while the counts are being worked out.
 *
 * <p>Three states and not one. A declaration the rising has not reached is at the bottom: nothing has
 * been shown of it, which is where a rising starts and is not the same as having been shown to have
 * no value. A declaration whose reading came to none while resting on one of those is
 * <em>withheld</em> — it has an answer and no proof of it, because what it rests on has not been
 * shown anything. Only the third is settled.
 *
 * <p>Keeping them apart is what stops a proof being written out of an assumption. With one state for
 * all three, {@code A} would carry "no value, because {@code B} has none" while {@code B} carried the
 * same about {@code A}, and neither would have been shown anything.
 *
 * <p>What withholds a reading is the reading and not the shape of the proof it wrote. A reading that
 * reaches a name nothing has been shown of is withheld whatever it made of it, so a reading added
 * later cannot settle on an assumption by writing a proof that does not mention what it rested on.
 * That is what {@link #read} is for: it is the only way to take a reading, and it answers with what
 * the reading rested on beside what it came to.
 *
 * <p>What a reading takes from any of the three is the same, which is why they can live in one place.
 * A declaration reached by name is read for its count alone and its proof is left where it is, so a
 * name not yet shown anything and a name shown to have none both answer
 * {@link Emptiness.TheNameHasNone} — true of the second already, and of the first once the rising has
 * stopped with it still withheld. {@link TypeCardinality} is where that is made good.
 */
final class Answers {

    /** What the rising has arrived at for one declaration. */
    private sealed interface Answer {

        /** Nothing has been shown of it yet. */
        record AtBottom() implements Answer {}

        /** It came to none on a reading that rested on something nothing has been shown of. */
        record Withheld(Cardinality.None count) implements Answer {}

        /** What it comes to. */
        record Settled(Cardinality count) implements Answer {}
    }

    /** What one declaration came to, and what the reading of it rested on. */
    record Reading(Cardinality count, boolean restedOnSomethingNotShown) {}

    private static final Answer AT_BOTTOM = new Answer.AtBottom();

    private final Map<TypeSymbol, Answer> by;
    private boolean rested;

    private Answers(Map<TypeSymbol, Answer> by) {
        this.by = by;
    }

    /** Nothing known of anything. */
    static Answers empty() {
        return new Answers(new HashMap<>());
    }

    /** The counts already worked out, with nothing left unshown. */
    static Answers settled(Map<TypeSymbol, Cardinality> counts) {
        Answers answers = empty();
        counts.forEach(answers::settle);
        return answers;
    }

    /**
     * One declaration read, with what the reading rested on.
     *
     * <p>The only way to take a reading. What is recorded is every name the reading reached that
     * nothing has been shown of, which is a fact about the reading and not about the proof it wrote —
     * so it holds however a reading chooses to say what it found.
     */
    Reading read(Supplier<Cardinality> reading) {
        rested = false;
        Cardinality count = reading.get();
        return new Reading(count, rested);
    }

    /** What {@code name} comes to. */
    void settle(TypeSymbol name, Cardinality count) {
        by.put(name, new Answer.Settled(count));
    }

    /** {@code name} came to none on a reading resting on something nothing has been shown of. */
    void withhold(TypeSymbol name, Cardinality.None count) {
        by.put(name, new Answer.Withheld(count));
    }

    /** Nothing shown of {@code name} yet, which is where a rising starts it. */
    void atBottom(TypeSymbol name) {
        by.put(name, AT_BOTTOM);
    }

    /** Whether the rising stopped with nothing shown of {@code name}. */
    boolean withheld(TypeSymbol name) {
        return by.get(name) instanceof Answer.Withheld;
    }

    /** What a withheld reading of {@code name} came to none by, which nothing has yet shown. */
    Emptiness withheldProof(TypeSymbol name) {
        return ((Answer.Withheld) by.get(name)).count().why();
    }

    /** What {@code name} last came to, or null while nothing has been read of it at all. */
    Cardinality cameTo(TypeSymbol name) {
        return switch (by.get(name)) {
            case Answer.Withheld withheld -> withheld.count();
            case Answer.Settled settled -> settled.count();
            case null, default -> null;
        };
    }

    /**
     * How many values {@code name} has, as a reading that reached it by name may take it.
     *
     * <p>Nothing is known of a name this never reached, which is the answer that refuses nothing. A
     * name with no value answers with the proof that stops at the name, whichever state it is in:
     * what is beyond the name is that declaration's own answer and is not carried here.
     */
    Cardinality of(TypeSymbol name) {
        Answer answer = by.get(name);
        if (answer == null) {
            return Cardinality.UNKNOWN;
        }
        if (answer instanceof Answer.Settled settled) {
            return settled.count() instanceof Cardinality.None
                    ? Cardinality.none(new Emptiness.TheNameHasNone(name))
                    : settled.count();
        }
        rested = true;
        return Cardinality.none(new Emptiness.TheNameHasNone(name));
    }

    /**
     * Every count settled, which every name reached has to be by the time the reading is over.
     *
     * <p>A name left withheld is one the rising stopped with nothing shown of, and it is the rising's
     * to answer for before anything else reads these. Answering with the absence of it would put a
     * type nothing can build back among the ones that can.
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
