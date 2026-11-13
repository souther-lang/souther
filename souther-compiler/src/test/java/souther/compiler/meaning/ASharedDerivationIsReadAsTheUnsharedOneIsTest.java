package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.semantics.ConditionJoin;

import java.time.Duration;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Optional;
import java.util.function.Supplier;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTimeoutPreemptively;

/**
 * A derivation that holds one step in more than one place says what the same derivation says made
 * of a step for each place, and is read in what grows with the steps and not with the ways to
 * them ({@link MeaningsOfABody.Meaning#relationsDownTheArmsOf},
 * {@link MeaningsOfABody.Meaning#relationsReadIn}, {@link MeaningsOfABody.Meaning#whereARunStops}).
 *
 * <p>Said once for each place the same step is read at the same arms: that is what sharing is for,
 * and a relation read on two different arms is still said once for each. So the two are compared
 * with a relation said once for each arm it is read on, in the order it is first said.
 */
class ASharedDerivationIsReadAsTheUnsharedOneIsTest {

    private static final Relation FIRST = relation("first");

    private static Relation relation(String name) {
        return new Relation.Affine(LinearForm.atom(new DecisionAtom.OfTheInput(
                new NumericTerm.ValueOf(TermPath.of(name)))), Rel.GT);
    }

    private static Derivation readOf(Relation relation) {
        return new Derivation.AComparisonRead(Derivation.ComparisonReading.BY_A_LAW, relation,
                true, Derivation.AComparisonRead.Facing.NOTHING_WRITTEN);
    }

    private static Derivation stop() {
        return new Derivation.TheRunStopsHere();
    }

    /**
     * Each level holds the one below it in the condition and in both arms of an {@code if}, or
     * twice in a join, beside a step of its own that no other level has. Where {@code shared} the
     * one below is one object; where not, each place holds a copy made of its own.
     */
    private static Derivation chain(int depth, boolean shared, Supplier<Derivation> bottom,
                                    java.util.function.IntFunction<Derivation> own) {
        if (depth == 0) {
            return bottom.get();
        }
        Derivation below = chain(depth - 1, shared, bottom, own);
        Derivation second = shared ? below : chain(depth - 1, false, bottom, own);
        Derivation third = shared ? below : chain(depth - 1, false, bottom, own);
        Derivation beside = own.apply(depth);
        return depth % 2 == 0
                ? new Derivation.IfThenElse(below,
                        new Derivation.Joined(ConditionJoin.BOTH, second, beside), third)
                : new Derivation.Joined(ConditionJoin.EITHER, below,
                        new Derivation.Joined(ConditionJoin.BOTH, second, beside));
    }

    /** What is said, once for each arm it is said on, in the order it is first said. */
    private static <T> List<T> onceForEach(List<T> said) {
        return new ArrayList<>(new LinkedHashSet<>(said));
    }

    @Test
    void theRelationsReadDownTheArmsAreTheOnesTheUnsharedDerivationSays() {
        Supplier<Derivation> bottom = () -> readOf(FIRST);
        Derivation shared = chain(5, true, bottom, level -> readOf(relation("level" + level)));
        Derivation unshared = chain(5, false, bottom, level -> readOf(relation("level" + level)));

        List<MeaningsOfABody.Meaning.ReadOnAnArm> said =
                MeaningsOfABody.Meaning.relationsDownTheArmsOf(shared);

        assertFalse(said.isEmpty());
        assertEquals(onceForEach(MeaningsOfABody.Meaning.relationsDownTheArmsOf(unshared)),
                onceForEach(said));
        assertEquals(onceForEach(MeaningsOfABody.Meaning.relationsReadIn(unshared)),
                onceForEach(MeaningsOfABody.Meaning.relationsReadIn(shared)));
    }

    @Test
    void aRelationReadOnTwoArmsIsStillSaidOnceForEach() {
        Derivation read = readOf(FIRST);
        Derivation condition = new Derivation.ATruthOfASubject(
                new DecisionSubject.AnInput(TermPath.of("a")), true);

        // One step, held by both arms of a choice: read on the arm taken and on the other.
        List<MeaningsOfABody.Meaning.ReadOnAnArm> said = MeaningsOfABody.Meaning
                .relationsDownTheArmsOf(new Derivation.IfThenElse(condition, read, read));

        Proposition taken = condition.concludes(Optional.empty());
        assertEquals(List.of(
                new MeaningsOfABody.Meaning.ReadOnAnArm(FIRST, Proposition.all(List.of(taken))),
                new MeaningsOfABody.Meaning.ReadOnAnArm(FIRST,
                        Proposition.all(List.of(taken.denied())))), said);
    }

    @Test
    void aStepAtWhichARunStopsIsSaidAsTheUnsharedDerivationSaysIt() {
        Derivation shared = chain(5, true, ASharedDerivationIsReadAsTheUnsharedOneIsTest::stop,
                level -> stop());
        Derivation unshared = chain(5, false, ASharedDerivationIsReadAsTheUnsharedOneIsTest::stop,
                level -> stop());

        Proposition whereItStops = new MeaningsOfABody.Meaning(Proposition.all(List.of()), shared)
                .whereARunStops();

        assertEquals(new MeaningsOfABody.Meaning(Proposition.all(List.of()), unshared)
                .whereARunStops(), whereItStops);
    }

    /** Where no arm is gone down the same step is said once, however many places hold it. */
    @Test
    void aStepHeldTwiceByEveryJoinOfAChainIsReadOnceForEachJoin() {
        Derivation read = readOf(FIRST);
        Derivation held = read;
        Derivation stops = stop();
        Derivation heldStop = stops;
        for (int at = 0; at < 40; at++) {
            held = new Derivation.Joined(ConditionJoin.BOTH, held, held);
            heldStop = new Derivation.Joined(ConditionJoin.EITHER, heldStop, heldStop);
        }
        Derivation chain = held;
        Derivation stopChain = heldStop;

        List<MeaningsOfABody.Meaning.ReadOnAnArm> said = assertTimeoutPreemptively(
                Duration.ofSeconds(30),
                () -> MeaningsOfABody.Meaning.relationsDownTheArmsOf(chain));
        List<Relation> relations = assertTimeoutPreemptively(Duration.ofSeconds(30),
                () -> MeaningsOfABody.Meaning.relationsReadIn(chain));
        Proposition stopped = assertTimeoutPreemptively(Duration.ofSeconds(30),
                () -> new MeaningsOfABody.Meaning(Proposition.all(List.of()), stopChain)
                        .whereARunStops());

        assertEquals(List.of(new MeaningsOfABody.Meaning.ReadOnAnArm(FIRST,
                Proposition.all(List.of()))), said);
        assertEquals(List.of(FIRST), relations);
        assertEquals(Proposition.all(List.of()), stopped);
    }
}
