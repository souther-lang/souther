package souther.compiler.inputs;

import souther.compiler.check.ElementsWrittenOut;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.OptionalInt;

/**
 * What a name a body reads stands for, said in terms of the behavior's input.
 *
 * <p>Seven answers rather than two. A reader that asks only which position a name is gets a
 * position or nothing, and that nothing holds six different names at once: one given arithmetic
 * over positions, one an operation handed an element of a container this reading can write out,
 * one of a container written out holding no element at all, one of a container it could write out
 * and holding more than it does, one it handed an element of a container it cannot, and one this
 * reading knows nothing about. Told apart nowhere, they were read the same way — so a rule written
 * over a name given arithmetic drew no line, and nothing said why.
 *
 * <p>Facts about the name and not permissions. Whether a reader may put {@link Through}'s expression
 * where the name stands is that reader's to settle from the fact; what is answered here is what the
 * reading of the input knows, which is the same knowledge whoever asks.
 *
 * <p><b>Which values, and never which one of them.</b> {@link Through} says the name and one value
 * are one value; {@link OneOf} names every value the name can take, however many that is;
 * {@link Element} says there are values and this reading cannot write them out. What a reader does
 * with a set is that reader's rule — the arithmetic reads every member and keeps what they agree on
 * — and choosing a member here would be this reading answering a question about a value with a fact
 * about a set.
 */
public sealed interface ReadMeaning {

    /**
     * The name is a position of the behavior's input: a place a row writes at.
     *
     * <p>A place, and refusing to be made without one. What this says of a name is exactly that
     * there is somewhere a row writes, and one made with nowhere would say it of no place while
     * every reader went on believing there was one.
     */
    record Position(TermPath path) implements ReadMeaning {

        public Position {
            Objects.requireNonNull(path, "a name at a position is at one");
        }
    }

    /**
     * The name and {@code denotes} are one value, which is what the name was given.
     *
     * <p>What is held is the expression rather than anything read off it. Which of the readings of a
     * value this expression carries — an affine form, the positions it mentions — is each reader's
     * own question, and answering one of them here would be this reading keeping an account of a
     * name that only one reader could use.
     */
    record Through(Denotation denotes) implements ReadMeaning {

        public Through {
            Objects.requireNonNull(denotes, "a name read through denotes something");
        }
    }

    /**
     * The name is handed each of {@code occurrences} in turn, each where what it was kept by holds,
     * and stands for no other value.
     *
     * <p>How many there are says nothing. A container written with one member, and an arm that left
     * one of several standing, both answer with one — and that is this answer with one member rather
     * than a name that denotes it: what a reader may do is state what every member supports, which
     * is the same rule at any count. A singleton read as a denotation would be a name given the
     * value of an element, which is what an arm is not evidence for.
     *
     * <p><b>Exhaustive, or this is not the answer.</b> What a reader may do with a plurality is
     * state what holds of every member, and one member left out makes that statement about a value
     * the name can take and nothing said. So this is produced only where every element the
     * container can hold was written down and reached — a list written out, or one an operation put
     * together of pieces of such a list ({@link WrittenOutElements}), narrowed by the arms passed
     * on the way — and any other container stays {@link Element}, which says the plurality is there
     * and its members are not in hand. A reading that cannot write them out is one capability
     * short; a reading that writes out some of them is wrong.
     *
     * <p><b>Which of them are there is decided once, by whoever can read a truth.</b> An occurrence
     * a filter dropped on every row is no element: no run hands it to a closure, and nothing stated
     * of it is part of anything. Whether a truth it was kept by holds on every row, on none, or
     * turns on the row is a reading of that truth, which this reading of names cannot make — so a
     * reader outside it is handed the occurrences only through what decides that
     * ({@link WhereKept}): {@link #occurrencesWhere} for where each application is made, and
     * {@link #valuesWhere} for what every value supports. What is left out there is left out for
     * every reader alike, and a reader cannot take an occurrence no run has.
     *
     * <p>Never empty as written. A container written with no element is {@link NoneHeld}, which is
     * an answer of its own; what a decision leaves of these may be none, and a reader handed none
     * reads it as that answer.
     *
     * <p>A list and not a set. Two members that are written alike are two elements of the container,
     * and what tells occurrences apart is not this reading's to decide: a reader that only wants to
     * know what they agree on may ignore how many there are, and one that identified them here
     * would have taken that decision for every reader.
     */
    final class OneOf implements ReadMeaning {

        private final List<Occurrence> occurrences;

        public OneOf(List<Occurrence> occurrences) {
            if (occurrences == null || occurrences.isEmpty()) {
                throw new IllegalArgumentException(
                        "a container holding none is NoneHeld, so these are not none");
            }
            this.occurrences = List.copyOf(occurrences);
        }

        /** Every occurrence handed in turn, each where nothing keeps it out. */
        public static OneOf ofEvery(List<Denotation> values) {
            return new OneOf(values.stream().map(Occurrence::always).toList());
        }

        /**
         * The occurrences there on some row, in order, each with the truths {@code kept} leaves
         * open — none where every one was dropped on every row.
         */
        public List<Occurrence> occurrencesWhere(WhereKept kept) {
            return decided(occurrences, kept);
        }

        /** The value of each occurrence there on some row, whatever it is kept by there. */
        public List<Denotation> valuesWhere(WhereKept kept) {
            return occurrencesWhere(kept).stream().map(Occurrence::value).toList();
        }

        /** Every occurrence as written, kept or not: for what a reading of names asks of the
         *  values themselves, where a value no run has supports what the rest support. */
        List<Occurrence> asWritten() {
            return occurrences;
        }

        /** The value of every occurrence as written ({@link #asWritten}). */
        List<Denotation> everyValueItMayBe() {
            return occurrences.stream().map(Occurrence::value).toList();
        }

        @Override
        public boolean equals(Object other) {
            return other instanceof OneOf that && occurrences.equals(that.occurrences);
        }

        @Override
        public int hashCode() {
            return occurrences.hashCode();
        }

        @Override
        public String toString() {
            return "OneOf" + occurrences;
        }
    }

    /**
     * {@code occurrences}, leaving out the ones {@code kept} says are dropped on every row and the
     * truths it says hold on every row.
     */
    static List<Occurrence> decided(List<Occurrence> occurrences, WhereKept kept) {
        List<Occurrence> out = new ArrayList<>();
        for (Occurrence each : occurrences) {
            List<Occurrence.Kept> open = kept.stillOpen(each.keptWhere());
            if (open != null) {
                out.add(open == each.keptWhere() ? each
                        : new Occurrence(each.value(), open, each.answered()));
            }
        }
        return out;
    }

    /**
     * Which of the truths an occurrence was kept by are still open: those that hold on some rows and
     * not on others. Null where one holds on no row, which leaves the occurrence out of the
     * container; one that holds on every row is no condition, and is left out of what is open.
     *
     * <p>A reading of truths, which is the reading of conditions this reading of names is beneath:
     * a reader holding one hands it here, and every reader holding one decides the same.
     */
    @FunctionalInterface
    interface WhereKept {

        /** Decides nothing: every occurrence is there, kept by every truth it was kept by. */
        WhereKept NOTHING_DECIDED = keptWhere -> keptWhere;

        List<Occurrence.Kept> stillOpen(List<Occurrence.Kept> keptWhere);
    }

    /**
     * An element of a container that holds none: a list written empty, or one an operation put
     * together of pieces each of which is empty.
     *
     * <p>No value at all, which is knowledge and not a lack of it. A closure handed the elements of
     * such a container is applied to none, so nothing in it is reached; read as an {@link Element},
     * the closure would be read once as it stands, as though some run applied it.
     */
    record NoneHeld() implements ReadMeaning {}

    /**
     * One element a container holds where every one of {@code keptWhere} holds, and {@code value}
     * where it is held.
     *
     * <p>What it was kept by is said as the truths read where each was decided, and not as one
     * statement: a filter's closure was applied to the element in the reading that handed it, and
     * a filter around that one to the element it was handed in turn. Read in any other names, the
     * same truth would be about another value.
     *
     * @param answered which application of the step that made {@code value} this is, where that is
     *                 also the run's own count of the step's applications
     *                 ({@link ElementsWrittenOut.Occurrence#answered})
     */
    record Occurrence(Denotation value, List<Kept> keptWhere, OptionalInt answered) {

        public Occurrence {
            Objects.requireNonNull(value, "an occurrence is of some value");
            keptWhere = List.copyOf(keptWhere);
            Objects.requireNonNull(answered,
                    "an occurrence is answered by some application or none");
        }

        /** An occurrence nothing keeps out. */
        public static Occurrence always(Denotation value) {
            return new Occurrence(value, List.of(), OptionalInt.empty());
        }

        /** The same occurrence, kept also where every one of {@code more} holds — those decided
         *  first. */
        public Occurrence keptAlsoWhere(List<Kept> more) {
            List<Kept> all = new ArrayList<>(more);
            all.addAll(keptWhere);
            return new Occurrence(value, all, answered);
        }

        /**
         * What an occurrence was kept by ({@link ElementsWrittenOut.Kept}), read where it was
         * decided. What it states is not this reading's to say: a reader of conditions says it,
         * and says it once for every reader of an occurrence.
         */
        public sealed interface Kept {

            /** A truth, and which way it came out, of the {@code application}th application of the
             *  step that made it ({@link ElementsWrittenOut.Kept.ATruth}). */
            record ATruth(Denotation truth, boolean holds, int application) implements Kept {

                public ATruth {
                    Objects.requireNonNull(truth, "an occurrence is kept by some truth");
                    if (application < 0) {
                        throw new IllegalArgumentException(
                                "applications are counted from none: " + application);
                    }
                }
            }

            /** The arm {@code part} of {@code fork} being the one a run takes
             *  ({@link ElementsWrittenOut.Kept.AnArm}). */
            record AnArm(Denotation fork, int part) implements Kept {

                public AnArm {
                    Objects.requireNonNull(fork, "an arm is an arm of some fork");
                }
            }
        }
    }

    /**
     * An element of a container that could be written out, holding more than this reading writes
     * out ({@link ElementsWrittenOut#MOST_WALKED}).
     *
     * <p>Beside {@link Element} and not folded into it. That one says this reading cannot name the
     * values; this one says it could and stopped at a figure, which is a limit a reader reports as
     * one rather than a capability this compiler lacks.
     */
    record MoreThanAreWrittenOut() implements ReadMeaning {}

    /**
     * An operation of the language handed the name an element of a container, no position of the
     * input holds those elements, and this reading cannot write out which values they are.
     *
     * <p>Which is not the same as knowing nothing. The name holds something, and what it holds is
     * one element of what an operation answered rather than the value the name has at a read — an
     * expression built from a closure's parameter, standing for every element at once. A reader that
     * put it where the name stands would state of one value what was written about all of them.
     *
     * <p>Beside {@link OneOf} and short of it by exactly what a reader would need: that one names
     * every value the position admits, and this one says there are several and stops. Held apart
     * because the two license different work and the difference is not a matter of degree — a
     * statement about all of them can be made from the first and cannot be made from the second.
     */
    record Element() implements ReadMeaning {}

    /** Nothing in this reading gives the name a meaning: no position, no value it was given, and no
     *  operation that handed it one. */
    record Unknown() implements ReadMeaning {}
}
