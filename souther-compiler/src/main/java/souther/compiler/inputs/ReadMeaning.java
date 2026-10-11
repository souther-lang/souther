package souther.compiler.inputs;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

/**
 * What a name a body reads stands for, said in terms of the behavior's input.
 *
 * <p>Six answers rather than two. A reader that asks only which position a name is gets a position
 * or nothing, and that nothing holds five different names at once: one given arithmetic over
 * positions, one an operation handed an element of a container this reading can write out, one of
 * a container it could write out and holding more than it does, one it handed an element of a
 * container it cannot, and one this reading knows nothing about. Told apart nowhere, they were read
 * the same way — so a rule written over a name given arithmetic drew no line, and nothing said why.
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
     * <p><b>Two readings, and each a reader names.</b> The values every occurrence may be
     * ({@link #everyValueItMayBe}) leave out what each was kept by, which is a set holding at least
     * every value the name takes: enough for a reader stating what all of them support, and no
     * evidence that any of them is there. The occurrences themselves are in the order a walk of the
     * container meets them, with what each was kept by, which is what a reader saying where an
     * application of a closure is made takes — an occurrence a filter dropped is one no run hands
     * the closure, and read without its condition it would be an application nothing makes.
     *
     * <p>Never empty. A name stands for something wherever it can be read, so no members is not a
     * name that can take no value — it is this reading having lost them, and a statement quantified
     * over nothing holds vacuously, which would make the emptiest answer the strongest one.
     *
     * <p>A list and not a set. Two members that are written alike are two elements of the container,
     * and what tells occurrences apart is not this reading's to decide: a reader that only wants to
     * know what they agree on may ignore how many there are, and one that identified them here
     * would have taken that decision for every reader.
     */
    record OneOf(List<Occurrence> occurrences) implements ReadMeaning {

        public OneOf {
            if (occurrences == null || occurrences.isEmpty()) {
                throw new IllegalArgumentException(
                        "a name stands for something, so its occurrences are not none");
            }
            occurrences = List.copyOf(occurrences);
        }

        /** Every occurrence handed in turn, each where nothing keeps it out. */
        public static OneOf ofEvery(List<Denotation> values) {
            return new OneOf(values.stream().map(Occurrence::always).toList());
        }

        /**
         * The value of every occurrence, whatever it was kept by: no value the name takes is left
         * out, and a value here may be one no run hands it.
         */
        public List<Denotation> everyValueItMayBe() {
            return occurrences.stream().map(Occurrence::value).toList();
        }
    }

    /**
     * One element a container holds where every one of {@code keptWhere} holds, and {@code value}
     * where it is held.
     *
     * <p>What it was kept by is said as the truths read where each was decided, and not as one
     * statement: a filter's closure was applied to the element in the reading that handed it, and
     * a filter around that one to the element it was handed in turn. Read in any other names, the
     * same truth would be about another value.
     */
    record Occurrence(Denotation value, List<Kept> keptWhere) {

        public Occurrence {
            Objects.requireNonNull(value, "an occurrence is of some value");
            keptWhere = List.copyOf(keptWhere);
        }

        /** An occurrence nothing keeps out. */
        public static Occurrence always(Denotation value) {
            return new Occurrence(value, List.of());
        }

        /** The same occurrence, kept also where every one of {@code more} holds — those decided
         *  first. */
        public Occurrence keptAlsoWhere(List<Kept> more) {
            List<Kept> all = new ArrayList<>(more);
            all.addAll(keptWhere);
            return new Occurrence(value, all);
        }

        /** A truth an occurrence was kept by, and which way it came out. */
        public record Kept(Denotation truth, boolean holds) {

            public Kept {
                Objects.requireNonNull(truth, "an occurrence is kept by some truth");
            }
        }
    }

    /**
     * An element of a container that could be written out, holding more than this reading writes
     * out ({@link WrittenOutElements#MOST_WALKED}).
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
