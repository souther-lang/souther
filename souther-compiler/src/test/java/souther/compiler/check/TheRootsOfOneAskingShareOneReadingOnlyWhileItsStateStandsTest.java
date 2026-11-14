package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.DefaultStdlib;
import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.inputs.ElementsMet;
import souther.compiler.inputs.ElementsNamed;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.LinearForm;
import souther.compiler.types.BinOp;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.concurrent.atomic.AtomicInteger;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The roots one asking starts are read through one reading while what it was made in stands, and
 * through a reading of their own once it does not — and a root comes to the same either way.
 *
 * <p>What a name came to is the answer of the reading and of what the reading had met of the
 * container's elements: a root that names an element is held to it, and a form read after it on
 * the same elements is refused the other elements of the container. Sharing what the names came to
 * past that would give a later root what only an earlier one could have been given, so the roots
 * share while nothing has been met, and a root read after one that met an element is read as it
 * would be read alone.
 *
 * <p>Held as what each root comes to and what each reading was asked to tell, over every chain of
 * four links whose leaves are a number of no element and one of each of two elements of one
 * container, and as counts where the sharing is what is measured.
 */
class TheRootsOfOneAskingShareOneReadingOnlyWhileItsStateStandsTest {

    private static final SourcePos POS = new SourcePos(1, 1);
    private static final BindingOwner OWNER = new BindingOwner.OfValue("m", "v");

    private static final ElementsNamed.Slot AN_ITEM = ElementsNamed.Slot.innermostOf(
            TermPath.of("x").then("items").element());
    private static final BindingId ELEMENT_A = new BindingId(OWNER, 90);
    private static final BindingId ELEMENT_B = new BindingId(OWNER, 91);

    /** The leaves: a number of no element, and one each of two elements of one container. */
    private static final BindingId PLAIN = new BindingId(OWNER, 100);
    private static final BindingId OF_A = new BindingId(OWNER, 101);
    private static final BindingId OF_B = new BindingId(OWNER, 102);
    private static final List<BindingId> LEAVES = List.of(PLAIN, OF_A, OF_B);

    private static ElementsNamed through(BindingId element) {
        return ElementsNamed.of(List.of(new ElementsNamed.Named(AN_ITEM, element)));
    }

    /** A reading that holds what it names to the elements it has met, and tells what it read. */
    private static final class Elemental implements AffineForms.Reading<String, String> {

        private final Map<BindingId, Core> given;
        private final ElementsMet met = new ElementsMet();
        private final Set<String> told;
        private final Map<BindingId, Integer> followed;

        Elemental(Map<BindingId, Core> given, Set<String> told,
                  Map<BindingId, Integer> followed) {
            this.given = given;
            this.told = told;
            this.followed = followed;
        }

        @Override
        public Symbols symbols() {
            return Symbols.none(DefaultStdlib.get());
        }

        @Override
        public DeclarationAccess declarations() {
            return DeclarationAccess.NONE;
        }

        @Override
        public LinearForm<String> leafOf(Core e, String at) {
            if (!(Core.withoutStanding(e) instanceof Core.Read read)
                    || given.containsKey(read.binding())) {
                return null;
            }
            told.add("read " + read.binding().ordinal());
            if ((read.binding().equals(OF_A) && !met.admits(through(ELEMENT_A)))
                    || (read.binding().equals(OF_B) && !met.admits(through(ELEMENT_B)))) {
                return null;
            }
            return LinearForm.atom("n" + read.binding().ordinal());
        }

        @Override
        public String inside(Core.LetIn li, String at) {
            return at;
        }

        @Override
        public ValueStanding.ReadThrough<String> readThrough(Core.Read read, String at) {
            Core value = given.get(read.binding());
            if (value == null) {
                return null;
            }
            followed.merge(read.binding(), 1, Integer::sum);
            return new ValueStanding.ReadThrough<>(value, at);
        }

        @Override
        public List<ValueStanding.ReadThrough<String>> alternativesOf(Core.Read read, String at) {
            return null;
        }

        @Override
        public boolean readsThrough(Core.FieldAccess fa, String at) {
            return false;
        }
    }

    private static Core.Read read(BindingId binding) {
        return new Core.Read("a" + binding.ordinal(), binding, Type.INT, POS);
    }

    /** {@code a[i] = a[i-1] + leaf[i]}, from {@code a0 = leaf[0]}. */
    private static Map<BindingId, Core> chain(List<BindingId> leaves) {
        Map<BindingId, Core> given = new HashMap<>();
        for (int i = 1; i < leaves.size(); i++) {
            given.put(new BindingId(OWNER, i), new Core.Binary(BinOp.ADD,
                    i == 1 ? read(leaves.getFirst()) : read(new BindingId(OWNER, i - 1)),
                    read(leaves.get(i)), Core.BinaryReading.AS_THEY_STAND,
                    ConstructOccurrence.unwritten(), Type.INT, POS));
        }
        return given;
    }

    private static List<Core> roots(int links) {
        List<Core> roots = new ArrayList<>();
        for (int i = 1; i < links; i++) {
            roots.add(read(new BindingId(OWNER, i)));
        }
        return roots;
    }

    /** What a root came to, which is its form or that it stopped. */
    private static String cameTo(AffineForms.Outcome<String, String> outcome) {
        return outcome instanceof AffineForms.Outcome.Composed<String, String> composed
                ? composed.form().toString() : "stopped";
    }

    /** Every root read through a reading of its own. */
    private static List<String> aloneEach(Map<BindingId, Core> given, List<Core> roots,
                                          Set<String> told) {
        List<String> came = new ArrayList<>();
        for (Core root : roots) {
            Elemental reading = new Elemental(given, told, new HashMap<>());
            came.add(cameTo(AffineForms.outcome(root, "env", reading)));
        }
        return came;
    }

    /** Every root read through the roots of one asking, whose state stands while nothing is met. */
    private static List<String> sharing(Map<BindingId, Core> given, List<Core> roots,
                                        Set<String> told, AtomicInteger made,
                                        Map<BindingId, Integer> followed) {
        Elemental[] current = new Elemental[1];
        AffineForms.Roots<String, String> asking = new AffineForms.Roots<>(() -> {
            made.incrementAndGet();
            current[0] = new Elemental(given, told, followed);
            return current[0];
        }, () -> current[0].met.untouched());
        List<String> came = new ArrayList<>();
        for (Core root : roots) {
            came.add(cameTo(asking.outcome(root, "env")));
        }
        return came;
    }

    /**
     * Whatever the leaves of the chain are, each root comes to what it comes to alone, and the
     * readings are told the same of what they read.
     */
    @Test
    void everyRootComesToWhatItComesToAloneWhateverTheLeavesOfTheChainAre() {
        int links = 4;
        int chains = 0;
        for (int code = 0; code < Math.round(Math.pow(LEAVES.size(), links)); code++) {
            List<BindingId> leaves = new ArrayList<>();
            for (int at = 0, rest = code; at < links; at++, rest /= LEAVES.size()) {
                leaves.add(LEAVES.get(rest % LEAVES.size()));
            }
            Map<BindingId, Core> given = chain(leaves);
            // The leaves each alone, which no root contains another of, and then the chain's.
            List<Core> roots = new ArrayList<>(leaves.stream()
                    .map(TheRootsOfOneAskingShareOneReadingOnlyWhileItsStateStandsTest::read)
                    .map(Core.class::cast).toList());
            roots.addAll(roots(links));
            Set<String> toldAlone = new TreeSet<>();
            Set<String> toldSharing = new TreeSet<>();

            List<String> alone = aloneEach(given, roots, toldAlone);
            List<String> together = sharing(given, roots, toldSharing, new AtomicInteger(),
                    new HashMap<>());

            assertEquals(alone, together, "the leaves " + leaves);
            assertEquals(toldAlone, toldSharing, "the leaves " + leaves);
            chains++;
        }
        assertEquals(81, chains);
    }

    /** How often the name followed most was followed, over the roots of a chain of {@code links}
     *  numbers of no element, each root read through one reading or each through its own. */
    private static int mostFollowed(int links, boolean oneReading) {
        List<BindingId> leaves = new ArrayList<>();
        for (int at = 0; at < links; at++) {
            leaves.add(PLAIN);
        }
        Map<BindingId, Core> given = chain(leaves);
        Map<BindingId, Integer> followed = new HashMap<>();
        if (oneReading) {
            sharing(given, roots(links), new TreeSet<>(), new AtomicInteger(), followed);
        } else {
            for (Core root : roots(links)) {
                AffineForms.outcome(root, "env", new Elemental(given, new TreeSet<>(), followed));
            }
        }
        return followed.values().stream().mapToInt(Integer::intValue).max().orElse(0);
    }

    /**
     * Roots that meet no element share one reading, and what the names came to is followed as
     * often however many roots ask for it. Roots of readings of their own follow a name once for
     * each root above it, which is what holding it is measured against.
     */
    @Test
    void rootsThatMeetNoElementShareOneReading() {
        List<BindingId> leaves = List.of(PLAIN, PLAIN, PLAIN, PLAIN, PLAIN, PLAIN);
        AtomicInteger made = new AtomicInteger();

        sharing(chain(leaves), roots(leaves.size()), new TreeSet<>(), made, new HashMap<>());

        assertEquals(1, made.get(), "a reading was made for a root that met nothing");
        assertEquals(mostFollowed(6, true), mostFollowed(24, true),
                "a name was followed again by a root above it");
        assertTrue(mostFollowed(24, false) > mostFollowed(24, true),
                "roots that hold nothing for each other follow a name once for each root above");
    }

    /** The root after one that named an element is read through a reading made for it. */
    @Test
    void theRootAfterOneThatMetAnElementIsReadThroughAReadingOfItsOwn() {
        List<BindingId> leaves = List.of(OF_A, OF_B, PLAIN, PLAIN);
        Map<BindingId, Core> given = chain(leaves);
        AtomicInteger made = new AtomicInteger();

        List<String> came = sharing(given, roots(leaves.size()), new TreeSet<>(), made,
                new HashMap<>());

        assertEquals(List.of("stopped", "stopped", "stopped"), came.stream()
                .map(each -> each.equals("stopped") ? each : "composed").toList(),
                "a number of two elements of one container is read beside the other");
        assertEquals(3, made.get(), "each root met an element, and the next was read afresh");
    }

    /** Where the state the reading was made in has changed, the next root is read afresh. */
    @Test
    void aRootIsReadAfreshWhereWhatTheReadingWasMadeInHasChanged() {
        List<BindingId> leaves = List.of(PLAIN, PLAIN, PLAIN, PLAIN);
        Map<BindingId, Core> given = chain(leaves);
        AtomicInteger made = new AtomicInteger();
        boolean[] stands = {true};
        AffineForms.Roots<String, String> asking = new AffineForms.Roots<>(() -> {
            made.incrementAndGet();
            return new Elemental(given, new TreeSet<>(), new HashMap<>());
        }, () -> stands[0]);
        List<Core> roots = roots(leaves.size());

        assertNotNull(asking.outcome(roots.get(0), "env"));
        assertNotNull(asking.outcome(roots.get(1), "env"));
        assertEquals(1, made.get());
        stands[0] = false;
        assertNotNull(asking.outcome(roots.get(2), "env"));
        assertEquals(2, made.get());
        assertFalse(stands[0]);
    }
}
