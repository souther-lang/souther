package souther.compiler.partition;

import souther.compiler.coverage.ArmProbe;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.SourceConstructOrigin;

import java.util.List;
import java.util.Map;
import java.util.Objects;

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
     *                    at each — every site of the arm the classes carry the sibling at
     */
    record OfAnArm(SourceConstructOrigin fork, int part, int with, List<ArmProbe> occurrences,
                   Map<Integer, Integer> replacing) implements ReplacementOwed {

        public OfAnArm {
            Objects.requireNonNull(fork, "an arm is an arm of some fork");
            occurrences = List.copyOf(occurrences);
            replacing = Map.copyOf(replacing);
            if (occurrences.isEmpty() || replacing.isEmpty()) {
                throw new IllegalArgumentException("a replacement of an arm is looked for where a run"
                        + " through the arm is recorded and asked for where the classes carry it");
            }
        }

        @Override
        public Replacement replacement() {
            return new Replacement.OfAnArm(fork, part, with);
        }
    }

    /**
     * The body answering {@code answer} whatever it is given: the one answer the rows of the
     * behavior came to, which is the rewrite they cannot tell from the body.
     */
    record ByOneAnswer(ObservedValue answer) implements ReplacementOwed {

        public ByOneAnswer {
            Objects.requireNonNull(answer, "a body answering one value answers some value");
            if (answer.unread() != null) {
                throw new IllegalArgumentException("a body answering one value answers a value read"
                        + " in full: " + answer);
            }
        }

        @Override
        public Replacement replacement() {
            return new Replacement.ByOneAnswer();
        }
    }
}
