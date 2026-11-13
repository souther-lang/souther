package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.DefaultStdlib;
import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.numeric.LinearForm;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.Type;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * The reason a stop gives is a reading of the arguments that stopped under it, which is a reading
 * of every name they are made of; a walk asked for a form and nothing else, over a reading that is
 * told nothing of what it reads, leaves them unread.
 *
 * <p>Counted by the reading, as {@link ANameReadTwiceIsFollowedOnceTest} counts: what a reading is
 * asked is the one thing a caller of the walk decides, and a chain read to its end for every part
 * of a body that asks for a form is what the reason costs.
 */
class AStopIsGivenItsReasonOnlyWhereTheReasonIsKeptTest {

    private static final SourcePos POS = new SourcePos(1, 1);

    private static final BindingOwner OWNER = new BindingOwner.OfValue("m", "v");

    private static final int LINKS = 8;

    /** A name and the call it stands for, for each link, and the name nothing was given. */
    private static final int EVERY_PART = 2 * LINKS + 1;

    /** Nothing is an atom, so every link is a call the walk has no rule for. */
    private record Counting(Map<BindingId, Core> given, Map<Core, Integer> leaves,
                            boolean tells) implements AffineForms.Reading<String, Counting> {

        @Override
        public Symbols symbols() {
            return Symbols.none(DefaultStdlib.get());
        }

        @Override
        public DeclarationAccess declarations() {
            return DeclarationAccess.NONE;
        }

        @Override
        public boolean tellsWhatItReads() {
            return tells;
        }

        @Override
        public LinearForm<String> leafOf(Core e, Counting at) {
            leaves.merge(Core.withoutStanding(e), 1, Integer::sum);
            return null;
        }

        @Override
        public Counting inside(Core.LetIn li, Counting at) {
            return at;
        }

        @Override
        public ValueStanding.ReadThrough<Counting> readThrough(Core.Read read, Counting at) {
            Core value = given.get(read.binding());
            return value == null ? null : new ValueStanding.ReadThrough<>(value, at);
        }

        @Override
        public List<ValueStanding.ReadThrough<Counting>> alternativesOf(Core.Read read,
                                                                        Counting at) {
            return null;
        }

        @Override
        public boolean readsThrough(Core.FieldAccess fa, Counting at) {
            return false;
        }
    }

    private static Core.Read read(int link) {
        return new Core.Read("a" + link, new BindingId(OWNER, link), Type.INT, POS);
    }

    /** {@code a[i] = call(a[i-1])}, a call the library states no form of, over a first link
     *  nothing was given. */
    private static void chain(Map<BindingId, Core> given) {
        for (int i = 1; i <= LINKS; i++) {
            given.put(new BindingId(OWNER, i), new Core.Call(Core.Emitted.BUILD_LIST,
                    List.of(read(i - 1)), ConstructOccurrence.unwritten(),
                    Core.CallSettlement.None.INSTANCE, Type.INT, POS));
        }
    }

    private static Counting reading(boolean tells) {
        Map<BindingId, Core> given = new HashMap<>();
        chain(given);
        return new Counting(given, new HashMap<>(), tells);
    }

    @Test
    void aFormAskedOfAReadingToldNothingLeavesTheArgumentsOfAStopUnread() {
        Counting reading = reading(false);

        assertNull(AffineForms.of(read(LINKS), reading, reading));

        assertEquals(2, reading.leaves().size(),
                "the name asked about and the call it stands for, and nothing of what they are made of");
    }

    @Test
    void aFormAskedOfAReadingThatKeepsWhatItReadsReadsEveryNameTheStopIsMadeOf() {
        Counting reading = reading(true);

        assertNull(AffineForms.of(read(LINKS), reading, reading));

        assertEquals(EVERY_PART, reading.leaves().size());
    }

    @Test
    void theReasonOfAStopIsAskedForByTheOutcomeWhateverTheReadingKeeps() {
        Counting reading = reading(false);

        AffineForms.outcome(read(LINKS), reading, reading);

        assertEquals(EVERY_PART, reading.leaves().size());
    }
}
