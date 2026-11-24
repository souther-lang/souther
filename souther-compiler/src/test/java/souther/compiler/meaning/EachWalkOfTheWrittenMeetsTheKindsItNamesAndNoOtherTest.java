package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The walks over what a statement writes ask {@link Proposition#partsHeld} for the parts of the
 * kinds they go through, and no walk goes through a kind it did not before.
 *
 * <p>Each walk has its table here, with every kind that holds statements placed in it: gone into
 * or left. A kind added to {@code Proposition} is no kind of the table until it is placed, so the
 * test that reads the kinds off the class stops there, and a walk made to go into a kind it
 * skipped fails where that kind is asked.
 */
class EachWalkOfTheWrittenMeetsTheKindsItNamesAndNoOtherTest {

    private static final TermPath NODE = TermPath.of("o").then("node");
    private static final TermPath IN = NODE.then("a");
    private static final TermPath ALSO_IN = NODE.then("b");
    private static final TermPath OUT = TermPath.of("o").then("other");
    private static final TermPath ALSO_OUT = TermPath.of("o").then("another");
    private static final DecisionSubject CONTAINER_IN =
            new DecisionSubject.AnInput(NODE.then("kids"));
    private static final DecisionSubject CONTAINER_OUT = new DecisionSubject.AnInput(OUT);

    private static Proposition truthAt(TermPath at) {
        return new Proposition.Truth(new DecisionSubject.AnInput(at), true);
    }

    private static Set<Class<?>> classes(List<Class<? extends Proposition>> kinds) {
        return new LinkedHashSet<>(kinds);
    }

    /** Every kind that holds statements is gone into by the walk or left by it, and no more. */
    private static void placesEveryKind(Set<Class<?>> goneInto, Set<Class<?>> left) {
        Set<Class<?>> placed = new LinkedHashSet<>(goneInto);
        placed.addAll(left);
        assertEquals(classes(CompoundSamples.COMPOUNDS), placed);
        assertTrue(goneInto.stream().noneMatch(left::contains));
    }

    @Test
    void everyKindProposesIsPlacedHere() {
        assertEquals(CompoundSamples.permitted(), CompoundSamples.placed());
    }

    private static final Set<Class<?>> READS_PARTS = Set.of(
            Proposition.All.class, Proposition.Any.class, Proposition.WhereItAnswers.class,
            Proposition.OnAnApplication.class, Proposition.SoManyHold.class,
            Proposition.OfTheWays.class, Proposition.Some.class);
    private static final Set<Class<?>> READS_NO_PARTS = Set.of(Proposition.SomeReachable.class);

    /** Whether {@code stated}, read of the node, says the same of any node. */
    private static boolean movesWithTheNode(Proposition stated) {
        return WrittenOfANode.movesWithIt(stated, NODE, List.of());
    }

    @Test
    void theNodeIsReadThroughTheKindsItNamesAndNoOther() {
        placesEveryKind(READS_PARTS, READS_NO_PARTS);
        for (Class<?> kind : CompoundSamples.COMPOUNDS) {
            Proposition around = CompoundSamples.holding(kind, truthAt(IN), truthAt(ALSO_IN),
                    CONTAINER_IN);
            if (kind == Proposition.OfTheWays.class) {
                // What it is written out as is the statement the node is read of.
                assertEquals(movesWithTheNode(((Proposition.OfTheWays) around).written()),
                        movesWithTheNode(around), kind.getSimpleName());
            } else {
                assertEquals(READS_PARTS.contains(kind), movesWithTheNode(around),
                        kind.getSimpleName());
            }
        }
    }

    @Test
    void aPartOutsideTheNodeKeepsTheKindsItGoesIntoFromBeingReadOfIt() {
        for (Class<?> kind : READS_PARTS) {
            assertFalse(movesWithTheNode(CompoundSamples.holding(kind, truthAt(OUT),
                    truthAt(ALSO_OUT), CONTAINER_IN)), kind.getSimpleName());
        }
        for (Class<?> kind : CompoundSamples.TWO_PARTS) {
            if (READS_PARTS.contains(kind)) {
                assertFalse(movesWithTheNode(CompoundSamples.holding(kind, truthAt(IN),
                        truthAt(OUT), CONTAINER_IN)), kind.getSimpleName());
                assertFalse(movesWithTheNode(CompoundSamples.holding(kind, truthAt(OUT),
                        truthAt(IN), CONTAINER_IN)), kind.getSimpleName());
            }
        }
    }

    /** The container a quantifier names is a place it reads, which its part does not say. */
    @Test
    void theContainerOfAQuantifierIsReadAsWellAsItsPart() {
        assertTrue(movesWithTheNode(new Proposition.Some(CONTAINER_IN, truthAt(IN), true)));
        assertFalse(movesWithTheNode(new Proposition.Some(CONTAINER_OUT, truthAt(IN), true)));
    }

    /** The nodes reachable are left, whatever they hold at a node. */
    @Test
    void theNodesReachableAreNotReadOfTheNodeWhateverTheyHoldAtOne() {
        Proposition reached = CompoundSamples.holding(Proposition.SomeReachable.class,
                truthAt(IN), truthAt(ALSO_IN), CONTAINER_IN);
        assertFalse(movesWithTheNode(reached));
        assertFalse(movesWithTheNode(new Proposition.All(List.of(truthAt(IN), reached))));
        assertFalse(movesWithTheNode(new Proposition.WhereItAnswers(truthAt(IN), reached)));
    }

    private static Optional<List<TermPath>> placesRead(Proposition stated) {
        return PositionsAStatementReads.of(stated);
    }

    @Test
    void thePlacesAreReadThroughTheKindsItNamesAndNoOther() {
        placesEveryKind(READS_PARTS, READS_NO_PARTS);
        for (Class<?> kind : CompoundSamples.COMPOUNDS) {
            Proposition around = CompoundSamples.holding(kind, truthAt(IN), truthAt(ALSO_IN),
                    CONTAINER_IN);
            Optional<List<TermPath>> read = placesRead(around);
            String named = kind.getSimpleName();
            if (kind == Proposition.OfTheWays.class) {
                assertEquals(placesRead(((Proposition.OfTheWays) around).written()), read, named);
            } else if (kind == Proposition.Some.class) {
                // The container is read before the part it quantifies over.
                assertEquals(Optional.of(List.of(NODE.then("kids"), IN)), read, named);
            } else if (READS_PARTS.contains(kind)) {
                assertEquals(Optional.of(List.of(IN, ALSO_IN)), read, named);
            } else {
                assertEquals(Optional.empty(), read, named);
            }
        }
    }

    @Test
    void theNodesReachableAreNoPlacesToReadWhateverTheyHold() {
        Proposition reached = CompoundSamples.holding(Proposition.SomeReachable.class,
                truthAt(IN), truthAt(ALSO_IN), CONTAINER_IN);
        assertEquals(Optional.empty(), placesRead(reached));
        assertEquals(Optional.empty(),
                placesRead(new Proposition.All(List.of(truthAt(IN), reached))));
    }

    /** Each relation a statement holds, in the order met, by the spelling it is held under. */
    private static List<Proposition.Compared> relationsHeld(Proposition stated) {
        Map<Spelling, Proposition.Compared> found = new LinkedHashMap<>();
        WrittenLines.gather(stated, new LinkedHashSet<>(), found);
        return new ArrayList<>(found.values());
    }

    private static final Proposition.Compared ONE = CompoundSamples.numberAtLeastZero("x");
    private static final Proposition.Compared OTHER = CompoundSamples.numberAtLeastZero("y");

    /** The statements of a count are kept in the order of their keys, which is the order they are
     *  met in below. */
    @Test
    void theRelationsSampledAreInTheOrderOfTheirKeys() {
        assertTrue(ONE.spelling().compareTo(OTHER.spelling()) < 0);
        assertTrue(truthAt(IN).spelling().compareTo(truthAt(ALSO_IN).spelling()) < 0);
    }

    /** Every kind that holds statements is gone into, in the order it holds them. */
    @Test
    void theRelationsAreGatheredThroughEveryKindInTheOrderItHoldsThem() {
        for (Class<?> kind : CompoundSamples.COMPOUNDS) {
            Proposition around = CompoundSamples.holding(kind, ONE, OTHER, CONTAINER_IN);
            List<Proposition.Compared> held = relationsHeld(around);
            String named = kind.getSimpleName();
            if (kind == Proposition.OfTheWays.class) {
                assertEquals(relationsHeld(((Proposition.OfTheWays) around).written()), held,
                        named);
                assertTrue(held.contains(ONE), named);
            } else if (CompoundSamples.TWO_PARTS.contains(kind)) {
                assertEquals(List.of(ONE, OTHER), held, named);
            } else {
                assertEquals(List.of(ONE), held, named);
            }
        }
    }

    /** The node with nothing below it is met after the node, and not at all where there is none. */
    @Test
    void theNodesReachableGiveWhatIsSaidOfNothingBelowAfterWhatIsSaidAtANode() {
        TermPath t = TermPath.of("t");
        Proposition.SomeReachable with = new Proposition.SomeReachable(t, t, List.of("children"),
                ONE, Optional.of(OTHER), true);
        Proposition.SomeReachable without = new Proposition.SomeReachable(t, t,
                List.of("children"), ONE, Optional.empty(), true);

        assertEquals(List.of(ONE, OTHER), relationsHeld(with));
        assertEquals(List.of(ONE), relationsHeld(without));
    }

    @Test
    void aStatementHoldingNoStatementGathersWhatItIs() {
        assertEquals(List.of(ONE), relationsHeld(ONE));
        assertEquals(List.of(), relationsHeld(truthAt(IN)));
    }
}
