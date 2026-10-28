package souther.compiler.partition;

import souther.compiler.coverage.ArmProbe;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.SourceConstructOrigin;

import java.util.Collections;
import java.util.List;
import java.util.Objects;
import java.util.SequencedMap;
import java.util.TreeMap;

/**
 * A rewrite of a behavior's body no row was seen to tell from the body as written, as a search for
 * a row that would is put to it.
 *
 * <p>What is asked is an input on which the rewrite answers differently. Such an input is what a row
 * stating that answer would notice the rewrite by, and finding one is what shows the rewrite is not
 * the body under another spelling. Not finding one shows nothing: the search looked where it looked.
 *
 * <p>A value, because the plan it stands in is held by an answer a store keeps.
 */
public sealed interface ReplacementOwed {

    /** Which rewrite this is, apart from where it is looked for and what it would answer. */
    Replacement replacement();

    /**
     * Arm {@code part} of {@code fork} answering as its sibling {@code with} does.
     *
     * @param occurrences every place a run through the arm is recorded, which is where a row for
     *                    it is looked for; a row has to go through one of them to be asked anything
     * @param replacing   the sites a run asks to answer with the sibling, and the part it asks for
     *                    at each — every site of the arm the classes carry the sibling at, in the
     *                    order of the sites
     * @param seenThrough the inputs of each row stating its answer that a run was seen taking
     *                    through one of {@code occurrences}, in the order the rows are written.
     *                    Never empty: a rewrite of an arm is asked about because such a row went
     *                    through it, and those inputs are somewhere a run through the arm is known
     *                    to start from whatever a reading of the way in could state
     * @param ranWith     the inputs the rows of the module ran with, by the type of the position:
     *                    where an element of a list the classes divide no way is looked for
     */
    record OfAnArm(SourceConstructOrigin fork, int part, int with, List<ArmProbe> occurrences,
                   SequencedMap<Integer, Integer> replacing,
                   List<List<ObservedValue>> seenThrough,
                   InputsRowsRanWith ranWith) implements ReplacementOwed {

        public OfAnArm {
            Objects.requireNonNull(fork, "an arm is an arm of some fork");
            Objects.requireNonNull(ranWith, "the rows of a module ran with something or nothing");
            occurrences = List.copyOf(occurrences);
            replacing = Collections.unmodifiableSequencedMap(new TreeMap<>(replacing));
            seenThrough = seenThrough.stream().map(List::copyOf).toList();
            if (occurrences.isEmpty() || replacing.isEmpty() || seenThrough.isEmpty()) {
                throw new IllegalArgumentException("a replacement of an arm is looked for where a run"
                        + " through the arm is recorded, from the rows seen going through it, and"
                        + " asked for where the classes carry it");
            }
        }

        @Override
        public Replacement replacement() {
            return new Replacement.OfAnArm(fork, part, with);
        }
    }

    /**
     * The body answering one value whatever it is given: a value the rows of the behavior came to,
     * which is the rewrite they did not tell from the body.
     *
     * @param answeredOn the inputs of each row stating its answer that the body answered in full, in
     *                   the order the rows are written. Somewhere a run is known to come back, which
     *                   is where a row the rewrite answers differently on is looked for beside the
     *                   values the classes offer
     * @param ranWith    the inputs the rows of the module ran with, by the type of the position:
     *                   where an element of a list the classes divide no way is looked for
     */
    record ByOneAnswer(Replacement.ByOneAnswer replacement,
                       List<List<ObservedValue>> answeredOn,
                       InputsRowsRanWith ranWith) implements ReplacementOwed {

        public ByOneAnswer {
            Objects.requireNonNull(replacement, "a body answering one value answers some value");
            Objects.requireNonNull(ranWith, "the rows of a module ran with something or nothing");
            answeredOn = answeredOn.stream().map(List::copyOf).toList();
        }

        public ByOneAnswer(Replacement.ByOneAnswer replacement,
                           List<List<ObservedValue>> answeredOn) {
            this(replacement, answeredOn, InputsRowsRanWith.NONE);
        }

        /** The value the rewritten body answers. */
        public ObservedValue answer() {
            return replacement.answer();
        }
    }
}
