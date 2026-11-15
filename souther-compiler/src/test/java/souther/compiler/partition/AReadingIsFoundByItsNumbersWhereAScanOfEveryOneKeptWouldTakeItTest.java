package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.inputs.DeclaredInput;
import souther.compiler.inputs.ElementsMet;
import souther.compiler.inputs.InputReads;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import java.util.function.IntUnaryOperator;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The readings kept at a node are told apart by numbers before any is compared, and a reading is
 * taken exactly where the comparisons alone, asked of every one kept, would take it: the numbers
 * only leave out the readings the comparisons would turn away.
 *
 * <p>Asked of {@link SharedReads} against a model that keeps every reading in a list and compares
 * each, over many reads of a few nodes, inputs and keys, with numbers that tell them apart and
 * with numbers that are the same for all of them, so that what stands between a reading kept and
 * being taken again is the comparisons.
 */
class AReadingIsFoundByItsNumbersWhereAScanOfEveryOneKeptWouldTakeItTest {

    private static final List<Core> NODES = List.of(
            new Core.Int(1, Type.INT, new SourcePos(1, 1)),
            new Core.Int(2, Type.INT, new SourcePos(1, 2)),
            new Core.Int(3, Type.INT, new SourcePos(1, 3)));
    private static final InputReads READS =
            InputReads.ofWhatIsDeclared(Map.of(), DeclaredInput.NONE);

    /** A key equal to another of its number, with the hash it is given. */
    private record AKey(int number, int hash) {

        @Override
        public int hashCode() {
            return hash;
        }
    }

    private static final class AScene implements SharedReads.Scene<Integer, Integer, String> {

        int input;
        final IntUnaryOperator numberOfInputs;

        AScene(IntUnaryOperator numberOfInputs) {
            this.numberOfInputs = numberOfInputs;
        }

        @Override
        public boolean mayShare() {
            return true;
        }

        @Override
        public Integer inputs() {
            return input;
        }

        @Override
        public boolean sameInputs(Integer then, Integer now, boolean askedAggregates,
                                  int consulted) {
            return then.equals(now);
        }

        @Override
        public int requiredInputsHash(Integer inputs) {
            return numberOfInputs.applyAsInt(inputs);
        }

        @Override
        public Integer guards() {
            return 0;
        }

        @Override
        public boolean sameGuards(Integer then, Integer now) {
            return then.equals(now);
        }

        @Override
        public ElementsMet elementsMet() {
            return ElementsMet.NONE;
        }

        @Override
        public int metCount() {
            return 0;
        }

        @Override
        public List<String> metSince(int from) {
            return List.of();
        }

        @Override
        public void meetAgain(List<String> parts) {
            // no part is met here
        }

        @Override
        public int startConsulting() {
            return 0;
        }

        @Override
        public int endConsulting(int before) {
            return 0;
        }

        @Override
        public void consultAgain(int more) {
            // nothing is consulted here
        }

        @Override
        public int aggregatesAsked() {
            return 0;
        }
    }

    /** What the model keeps: a node, an input and a key, the three the comparisons are asked of. */
    private record Kept(Core node, int input, int key) {}

    private void holdsToAScanOfEveryOneKept(IntUnaryOperator numberOfInputs,
                                            IntUnaryOperator numberOfKeys) {
        AScene scene = new AScene(numberOfInputs);
        SharedReads<Integer, Integer, String, String> reads = new SharedReads<>(scene);
        List<Kept> model = new ArrayList<>();
        Random chance = new Random(3251);
        int[] made = {0};
        int taken = 0;
        for (int step = 0; step < 4000; step++) {
            Core node = NODES.get(chance.nextInt(NODES.size()));
            scene.input = chance.nextInt(6);
            int number = chance.nextInt(6);
            AKey key = new AKey(number, numberOfKeys.applyAsInt(number));
            Kept asked = new Kept(node, scene.input, number);
            boolean kept = model.stream().anyMatch(one -> one.equals(asked));
            int before = made[0];
            reads.shared(node, READS, key, () -> {
                made[0]++;
                return "read";
            }, _ -> true);
            assertEquals(kept ? 0 : 1, made[0] - before,
                    "step " + step + ": " + asked + (kept ? " is kept" : " is not kept"));
            if (kept) {
                taken++;
            } else {
                model.add(asked);
            }
        }
        assertTrue(taken > 3000, "the reads must mostly be of what is kept, or nothing is found");
        Set<Kept> distinct = new HashSet<>(model);
        assertEquals(distinct.size(), model.size());
        assertEquals(made[0], model.size());
    }

    @Test
    void readingsToldApartByTheirNumbersAreTakenWhereAScanWouldTakeThem() {
        holdsToAScanOfEveryOneKept(Integer::hashCode, Integer::hashCode);
    }

    @Test
    void readingsWhoseNumbersAreAllTheSameAreToldApartByTheComparisons() {
        holdsToAScanOfEveryOneKept(_ -> 0, _ -> 0);
    }

    @Test
    void readingsToldApartByTheNumberOfTheInputsAloneAreToldApartByTheKeys() {
        holdsToAScanOfEveryOneKept(Integer::hashCode, _ -> 0);
    }

    @Test
    void readingsToldApartByTheNumberOfTheKeysAloneAreToldApartByTheInputs() {
        holdsToAScanOfEveryOneKept(_ -> 0, Integer::hashCode);
    }
}
