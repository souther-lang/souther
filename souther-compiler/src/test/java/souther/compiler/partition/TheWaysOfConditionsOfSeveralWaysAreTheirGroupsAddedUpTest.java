package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;
import souther.compiler.partition.OneOfEach.Step;
import souther.compiler.partition.OneOfEach.Walked;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The ways conditions of several ways come to: every way a row takes where the figure lets them
 * all be handed on, and otherwise some of them with the figure that left the rest — with the
 * looking for them the ways of each group that turns on positions in common, added up and not
 * multiplied, and a proof that nothing is past them only from a group walked to its end.
 */
class TheWaysOfConditionsOfSeveralWaysAreTheirGroupsAddedUpTest {

    private static final TermPath X = TermPath.of("x");
    private static final TermPath Y = TermPath.of("y");

    /** An entry: a position asked to be one of some values, or one of several lists of entries. */
    private sealed interface Entry {}

    private record Ask(TermPath at, Set<Integer> values) implements Entry {}

    private record Choice(List<List<Entry>> alternatives) implements Entry {}

    /** A choice that counts in {@code hashed} the times it is asked for its hash. */
    private record Hashed(List<List<Entry>> alternatives, AtomicInteger hashed) implements Entry {

        @Override
        public int hashCode() {
            hashed.incrementAndGet();
            return alternatives.hashCode();
        }
    }

    /** What is asked so far is the values left at each position; none left at one closes it,
     *  said by that position. */
    private static final OneOfEach.Vocabulary<Entry, Map<TermPath, Set<Integer>>, TermPath>
            VALUES = new OneOfEach.Vocabulary<>() {

                @Override
                public List<List<Entry>> alternatives(Entry entry) {
                    return switch (entry) {
                        case Choice choice -> choice.alternatives();
                        case Hashed hashed -> hashed.alternatives();
                        case Ask _ -> null;
                    };
                }

                @Override
                public Set<TermPath> positions(Entry entry) {
                    return entry instanceof Ask ask ? Set.of(ask.at()) : Set.of();
                }

                @Override
                public Map<TermPath, Set<Integer>> nothing() {
                    return Map.of();
                }

                @Override
                public Step<Map<TermPath, Set<Integer>>, TermPath> with(
                        Map<TermPath, Set<Integer>> so, Entry entry) {
                    if (!(entry instanceof Ask(TermPath at, Set<Integer> values))) {
                        return new Step.Held<>(so);
                    }
                    Set<Integer> left = new HashSet<>(so.getOrDefault(at, values));
                    left.retainAll(values);
                    if (left.isEmpty()) {
                        return new Step.Closed<>(at);
                    }
                    Map<TermPath, Set<Integer>> out = new LinkedHashMap<>(so);
                    out.put(at, left);
                    return new Step.Held<>(out);
                }
            };

    private static Ask ask(TermPath at, Integer... values) {
        return new Ask(at, Set.of(values));
    }

    private static Choice oneOf(Entry... alternatives) {
        List<List<Entry>> out = new ArrayList<>();
        for (Entry each : alternatives) {
            out.add(List.of(each));
        }
        return new Choice(out);
    }

    private static Walked<Entry, TermPath> walked(Entry... entries) {
        return OneOfEach.walk(List.of(entries), VALUES,
                CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT,
                CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG);
    }

    @SuppressWarnings("unchecked")
    private static Walked.Open<Entry, TermPath> open(Walked<Entry, TermPath> walked) {
        return assertInstanceOf(Walked.Open.class, walked, () -> "some way open: " + walked);
    }

    /** What each way asks, where every way chose every choice on it. */
    @SuppressWarnings("unchecked")
    private static List<List<Entry>> chosen(Walked.Open<Entry, TermPath> walked) {
        return walked.ways().stream().map(way -> ((OneOfEach.Way.Chosen<Entry>)
                assertInstanceOf(OneOfEach.Way.Chosen.class, way,
                        () -> "every choice chosen: " + walked)).entries()).toList();
    }

    /**
     * Two choices alike standing at two places are two choices, walked apart and handed on apart:
     * a way taking one of them one way and the other the other way says both, and neither is lost
     * for being equal to the other.
     */
    @Test
    @SuppressWarnings("unchecked")
    void twoChoicesAlikeAreBothSaidOfAWayThatTookThemApart() {
        Choice first = oneOf(ask(X, 1, 2), ask(X, 2, 3));
        Choice second = oneOf(ask(X, 1, 2), ask(X, 2, 3));
        assertEquals(first, second, "the two choices are alike");
        List<List<Integer>> taken = new ArrayList<>();
        for (OneOfEach.Way<Entry> way : open(walked(first, second)).ways()) {
            OneOfEach.Way.Chosen<Entry> chosen = assertInstanceOf(OneOfEach.Way.Chosen.class, way);
            assertEquals(2, chosen.choices().size(), () -> "both choices are said: " + chosen);
            taken.add(chosen.choices().stream().map(OneOfEach.Choice::alternative).toList());
        }
        assertTrue(taken.contains(List.of(0, 1)) && taken.contains(List.of(1, 0)),
                () -> "a way takes the two apart, either way round: " + taken);
    }

    /**
     * One choice standing at two places is two choices, as two alike are: which object an entry
     * is says nothing of where it stands, since a value made again may be handed out as the one
     * made before.
     */
    @Test
    @SuppressWarnings("unchecked")
    void oneChoiceAtTwoPlacesIsTwoChoicesAsTwoAlikeAre() {
        Choice twice = oneOf(ask(X, 1, 2), ask(X, 2, 3));
        List<List<Integer>> taken = new ArrayList<>();
        for (OneOfEach.Way<Entry> way : open(walked(twice, twice)).ways()) {
            OneOfEach.Way.Chosen<Entry> chosen = assertInstanceOf(OneOfEach.Way.Chosen.class, way);
            assertEquals(2, chosen.choices().size(), () -> "both places are said: " + chosen);
            taken.add(chosen.choices().stream().map(OneOfEach.Choice::alternative).toList());
        }
        assertEquals(Set.of(List.of(0, 0), List.of(0, 1), List.of(1, 0), List.of(1, 1)),
                new HashSet<>(taken), () -> "every way of the two places: " + taken);
    }

    /**
     * The way of an alternative of a nested choice that stands in two alternatives is looked for
     * through the place it stands at, and found where only the second place leads to it: held to
     * the first place's alternative, the looking would find that no way takes it there and leave
     * it out.
     */
    @Test
    void aNestedChoiceAtTwoPlacesHasTheWayOfEachAlternativeAtEitherLookedFor() {
        TermPath w = TermPath.of("w");
        TermPath v = TermPath.of("v");
        Ask third = ask(w, 3);
        Choice nested = oneOf(ask(w, 1, 2, 3), third);
        Choice first = new Choice(List.of(List.of(ask(w, 1), nested), List.of(ask(v, 1))));
        Choice second = new Choice(List.of(List.of(nested), List.of(ask(v, 2))));
        List<Entry> entries = new ArrayList<>(List.of(first, second));
        for (int each = 0; each < 5; each++) {
            entries.add(oneOf(ask(w, 1, 2, 3), ask(w, 1, 2, 3, 4)));
        }
        Walked.Open<Entry, TermPath> walked = open(walked(entries.toArray(Entry[]::new)));

        assertFalse(walked.everyWay(), () -> "more ways than are looked along: " + walked);
        assertTrue(chosen(walked).stream().anyMatch(way -> way.contains(third)),
                () -> "the nested choice's second alternative, past the second place: " + walked);
    }

    /**
     * Where the figure leaves room for a way per alternative of each condition and no more, a
     * condition standing at two places is owed its alternatives once: a way taking one at either
     * place takes it, and the room it would spend at the second goes to another condition's.
     */
    @Test
    @SuppressWarnings("unchecked")
    void aConditionAtTwoPlacesIsOwedEachAlternativeOnceWhereTheFigureIsTight() {
        Choice twice = oneOf(ask(X, 1, 2), ask(X, 1, 2, 3));
        List<Entry> entries = new ArrayList<>(List.of(twice, twice));
        int room = CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG.maximum();
        // The first way, one for the second alternative of the condition at two places, and one
        // for each other condition's: the figure exactly.
        for (int each = 0; each < room - 2; each++) {
            entries.add(oneOf(ask(X, 1, 2, 3), ask(X, 1, 2, 3, 10 + each)));
        }
        Walked.Open<Entry, TermPath> walked = open(walked(entries.toArray(Entry[]::new)));

        assertFalse(walked.everyWay(), () -> "more ways than are looked along: " + walked);
        Set<List<Object>> taken = new HashSet<>();
        for (OneOfEach.Way<Entry> way : walked.ways()) {
            OneOfEach.Way.Chosen<Entry> chosen = assertInstanceOf(OneOfEach.Way.Chosen.class, way);
            chosen.choices().forEach(each -> taken.add(List.of(each.entry(), each.alternative())));
        }
        for (Entry each : entries) {
            for (int alternative = 0; alternative < 2; alternative++) {
                List<Object> owed = List.of(each, alternative);
                assertTrue(taken.contains(owed), () -> "a way takes " + owed + ": " + taken);
            }
        }
    }

    /** {@link #VALUES}, answering alone where {@code alone} says, and counting what it is asked
     *  in {@code asked}. */
    private static OneOfEach.Vocabulary<Entry, Map<TermPath, Set<Integer>>, TermPath> counting(
            boolean alone, int[] asked) {
        return new OneOfEach.Vocabulary<>() {

            @Override
            public List<List<Entry>> alternatives(Entry entry) {
                return VALUES.alternatives(entry);
            }

            @Override
            public Set<TermPath> positions(Entry entry) {
                return VALUES.positions(entry);
            }

            @Override
            public Map<TermPath, Set<Integer>> nothing() {
                return VALUES.nothing();
            }

            @Override
            public Step<Map<TermPath, Set<Integer>>, TermPath> with(
                    Map<TermPath, Set<Integer>> so, Entry entry) {
                asked[0]++;
                return VALUES.with(so, entry);
            }

            @Override
            public boolean answersAlone() {
                return alone;
            }
        };
    }

    /**
     * An alternative that closes beside what the first choice took is looked for past it without
     * walking every way of the choices between: of a vocabulary that answers alone, what the way
     * has to take in is asked beside the first choice where it is taken, and the looking left
     * finds the way past the first choice's other alternative. Of one that does not, the walk asks
     * nothing ahead of where it stands, and the choices between use the looking up.
     */
    @Test
    void anAlternativeClosingBesideAnEarlyChoiceIsFoundPastItWhereTheVocabularyAnswersAlone() {
        TermPath w = TermPath.of("w");
        Ask past = ask(w, 2, 5);
        List<Entry> entries = new ArrayList<>();
        entries.add(oneOf(ask(w, 1), ask(w, 2)));
        // Between them, more ways than the looking reaches: every one open, and every one closing
        // where the last choice is taken past the first's first alternative.
        for (int each = 0; each < 12; each++) {
            entries.add(oneOf(ask(w, 1, 2, 3), ask(w, 1, 2, 3, 4)));
        }
        entries.add(oneOf(ask(w, 1, 2), past));

        Walked.Open<Entry, TermPath> alone = open(OneOfEach.walk(entries,
                counting(true, new int[1]), CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT,
                CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG));
        assertTrue(chosen(alone).stream().anyMatch(way -> way.contains(past)),
                () -> "the last choice's second alternative, past the first's second: " + alone);

        Walked.Open<Entry, TermPath> asked = open(walked(entries.toArray(Entry[]::new)));
        assertFalse(chosen(asked).stream().anyMatch(way -> way.contains(past)),
                () -> "nothing is asked ahead of a vocabulary that does not answer alone: "
                        + asked);
    }

    /**
     * What is asked ahead costs no more than the walk's own asking and what the way is held to,
     * once: each entry the walk takes is taken in beside what it carries ahead once, where the
     * walk takes it. Where nothing closes, the walk takes the same ways either way, so asking
     * ahead adds that and no more — and not what the way is held to again at every choice the
     * walk comes to on the way to it.
     */
    @Test
    void whatIsAskedAheadCostsNoMoreThanTheWalksOwnAskingAndWhatTheWayIsHeldToOnce() {
        TermPath w = TermPath.of("w");
        TermPath v = TermPath.of("v");
        List<Entry> heavy = new ArrayList<>();
        heavy.add(ask(w, 1, 2, 3, 4, 5));
        for (int each = 0; each < 1000; each++) {
            heavy.add(ask(v, 1, 2));
        }
        // First, so that the first ways all take its other alternative, and the way of this one
        // is looked for past every choice after it.
        List<Entry> entries = new ArrayList<>();
        entries.add(new Choice(List.of(List.of(ask(w, 1, 2)), heavy)));
        for (int each = 0; each < 30; each++) {
            entries.add(oneOf(ask(w, 1, 2, 3), ask(w, 1, 2, 3, 4)));
        }

        int[] plain = {0};
        Walked.Open<Entry, TermPath> asked = open(OneOfEach.walk(entries, counting(false, plain),
                CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT,
                CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG));
        int[] ahead = {0};
        Walked.Open<Entry, TermPath> alone = open(OneOfEach.walk(entries, counting(true, ahead),
                CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT,
                CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG));

        assertFalse(alone.everyWay(), () -> "more ways than are looked along: " + alone);
        assertEquals(asked.ways(), alone.ways(), "nothing closes, so the same ways either way");
        assertTrue(ahead[0] <= 2 * plain[0] + heavy.size(),
                () -> "asked " + ahead[0] + " times asking ahead, against " + plain[0]);
    }

    /**
     * A vocabulary holding nothing for what is taken in — whose state is null — has the way of
     * every alternative looked for and found where it asks ahead: what it holds is carried as the
     * step it came to, and never taken for the closing of what is asked ahead.
     */
    @Test
    @SuppressWarnings("unchecked")
    void aVocabularyWhoseStateIsNullHasTheWayOfEveryAlternativeFoundWhereItAsksAhead() {
        OneOfEach.Vocabulary<Entry, Object, TermPath> holdingNothing =
                new OneOfEach.Vocabulary<>() {

            @Override
            public List<List<Entry>> alternatives(Entry entry) {
                return VALUES.alternatives(entry);
            }

            @Override
            public Set<TermPath> positions(Entry entry) {
                return VALUES.positions(entry);
            }

            @Override
            public Object nothing() {
                return null;
            }

            @Override
            public Step<Object, TermPath> with(Object so, Entry entry) {
                return new Step.Held<>(null);
            }

            @Override
            public boolean answersAlone() {
                return true;
            }
        };
        List<Entry> entries = new ArrayList<>();
        for (int each = 0; each < 5; each++) {
            entries.add(oneOf(ask(X, 1, 10 + each), ask(X, 2, 10 + each)));
        }
        Walked<Entry, TermPath> walked = OneOfEach.walk(entries, holdingNothing,
                CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT,
                CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG);

        Walked.Open<Entry, TermPath> open = assertInstanceOf(Walked.Open.class, walked);
        assertFalse(open.everyWay(), () -> "more ways than are looked along: " + open);
        for (Entry each : entries) {
            Entry second = ((Choice) each).alternatives().get(1).getFirst();
            assertTrue(chosen(open).stream().anyMatch(way -> way.contains(second)),
                    () -> second + " has a way: " + open);
        }
    }

    /**
     * A closing is a value of its reason, however the reason came to be: one given and one worked
     * out where it is read are equal where the reasons are, and a closing for no reason is none.
     */
    @Test
    void aClosingIsItsReasonHoweverTheReasonIsWorkedOut() {
        Step.Closed<Object, TermPath> given = new Step.Closed<>(X);
        Step.Closed<Object, TermPath> workedOut = Step.Closed.workedOut(() -> TermPath.of("x"));

        assertEquals(given, workedOut, "equal for an equal reason");
        assertEquals(given.hashCode(), workedOut.hashCode());
        assertFalse(given.equals(new Step.Closed<>(Y)), "apart for another reason");
        Step.Closed<Object, TermPath> forNothing = Step.Closed.workedOut(() -> null);
        assertThrows(NullPointerException.class, forNothing::why, "a closing is for some reason");
    }

    /**
     * Whether an alternative is owed a way is asked of the condition only where the ways are more
     * than are handed on: a walk handing on every way never asks a condition for its hash, which
     * may walk all it says.
     */
    @Test
    void aWalkHandingOnEveryWayNeverAsksAConditionForItsHash() {
        AtomicInteger hashed = new AtomicInteger();
        Hashed onX = new Hashed(List.of(List.of(ask(X, 1)), List.of(ask(X, 2))), hashed);
        Hashed onY = new Hashed(List.of(List.of(ask(Y, 1)), List.of(ask(Y, 2))), hashed);

        assertTrue(open(walked(onX, onY)).everyWay(), "every way handed on");
        assertEquals(0, hashed.get(), "no condition asked for its hash");
    }

    /**
     * Held to the ways of every input of a few small choices, written out one by one: whatever
     * the walk hands on is a way along which what is asked holds together, every alternative of
     * every condition that some such way takes is taken by one handed on, and where none holds
     * together the walk says so — of a vocabulary asked ahead and of one that is not alike.
     *
     * <p>The choices are on one position or two, nested in each other, asking what others close
     * beside, and one standing at two places; few enough that the looking never runs out and
     * every alternative fits in the figure beside the first way, so that what is owed is all of
     * it. That the asking ahead is put to the test is counted: inputs where the ways are more
     * than are handed on, and where asking ahead left a branch the walk would have looked along —
     * those where the walk asking ahead asked less than the one that does not, which it can only
     * where it left one, since otherwise it takes the same ways and asks ahead beside them.
     */
    @Test
    @SuppressWarnings("unchecked")
    void whatTheWalkHandsOnIsHeldToEveryWayWrittenOutAskedAheadOrNot() {
        Random random = new Random(3028);
        int beyondTheFigure = 0;
        int leftByAsking = 0;
        for (int input = 0; input < 3000; input++) {
            List<Choice> made = new ArrayList<>();
            List<Entry> entries = new ArrayList<>();
            int length = 3 + random.nextInt(4);
            for (int each = 0; each < length; each++) {
                entries.add(random.nextInt(4) == 0 ? someAsk(random)
                        : someChoice(random, made, 1));
            }
            if (placesIn(entries) > 6 || owedIn(made) > 15) {
                continue;
            }
            Set<List<Object>> written = new HashSet<>();
            boolean anyHolds = false;
            for (WrittenOut way : writtenOut(entries)) {
                if (holdsTogether(way.asks())) {
                    anyHolds = true;
                    written.addAll(way.taken());
                }
            }
            int[] plain = {0};
            int[] ahead = {0};
            for (boolean alone : new boolean[] {false, true}) {
                Walked<Entry, TermPath> walked = OneOfEach.walk(entries,
                        counting(alone, alone ? ahead : plain),
                        CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT,
                        CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG);
                String said = entries + (alone ? " asked ahead" : "") + ": " + walked;
                if (!anyHolds) {
                    assertInstanceOf(Walked.Closed.class, walked, said);
                    continue;
                }
                Walked.Open<Entry, TermPath> open = assertInstanceOf(Walked.Open.class, walked,
                        said);
                Set<List<Object>> handed = new HashSet<>();
                for (OneOfEach.Way<Entry> way : open.ways()) {
                    OneOfEach.Way.Chosen<Entry> chosen =
                            assertInstanceOf(OneOfEach.Way.Chosen.class, way, said);
                    assertTrue(holdsTogether(chosen.entries()), () -> "holds together: " + said);
                    chosen.choices().forEach(each ->
                            handed.add(List.of(each.entry(), each.alternative())));
                }
                assertEquals(written, handed, () -> "every alternative a way takes: " + said);
                if (alone && !open.everyWay()) {
                    beyondTheFigure++;
                }
            }
            if (ahead[0] < plain[0]) {
                leftByAsking++;
            }
        }
        int beyond = beyondTheFigure;
        int left = leftByAsking;
        assertTrue(beyond > 200, () -> "inputs beyond the figure: " + beyond);
        assertTrue(left > 20, () -> "inputs where asking ahead left a branch: " + left);
    }

    /** One way of some entries written out: what it asks, and each choice it took as which. */
    private record WrittenOut(List<Ask> asks, List<List<Object>> taken) {}

    /** Every way of {@code entries}, each choice taken each way where it stands. */
    private static List<WrittenOut> writtenOut(List<Entry> entries) {
        List<WrittenOut> out = new ArrayList<>(List.of(new WrittenOut(List.of(), List.of())));
        for (Entry entry : entries) {
            List<WrittenOut> next = new ArrayList<>();
            for (WrittenOut before : out) {
                for (WrittenOut way : writtenOut(entry)) {
                    List<Ask> asks = new ArrayList<>(before.asks());
                    asks.addAll(way.asks());
                    List<List<Object>> taken = new ArrayList<>(before.taken());
                    taken.addAll(way.taken());
                    next.add(new WrittenOut(asks, taken));
                }
            }
            out = next;
        }
        return out;
    }

    private static List<WrittenOut> writtenOut(Entry entry) {
        if (entry instanceof Ask ask) {
            return List.of(new WrittenOut(List.of(ask), List.of()));
        }
        List<WrittenOut> out = new ArrayList<>();
        List<List<Entry>> alternatives = VALUES.alternatives(entry);
        for (int which = 0; which < alternatives.size(); which++) {
            for (WrittenOut way : writtenOut(alternatives.get(which))) {
                List<List<Object>> taken = new ArrayList<>();
                taken.add(List.of(entry, which));
                taken.addAll(way.taken());
                out.add(new WrittenOut(way.asks(), taken));
            }
        }
        return out;
    }

    /** Whether some value is left at every position {@code asked} asks of. */
    private static boolean holdsTogether(List<? extends Entry> asked) {
        Map<TermPath, Set<Integer>> so = VALUES.nothing();
        for (Entry each : asked) {
            if (VALUES.with(so, each) instanceof Step.Held<Map<TermPath, Set<Integer>>, TermPath>(
                    var held)) {
                so = held;
            } else {
                return false;
            }
        }
        return true;
    }

    private static Ask someAsk(Random random) {
        Set<Integer> values = new HashSet<>();
        for (int value = 1; value <= 3; value++) {
            if (random.nextInt(3) > 0) {
                values.add(value);
            }
        }
        values.add(1 + random.nextInt(3));
        return new Ask(random.nextBoolean() ? X : Y, values);
    }

    /** A choice of two alternatives of an entry or two, nested as deep as {@code depth} says —
     *  or, now and then, one made before, standing at another place. */
    private static Choice someChoice(Random random, List<Choice> made, int depth) {
        if (!made.isEmpty() && random.nextInt(5) == 0) {
            return made.get(random.nextInt(made.size()));
        }
        List<List<Entry>> alternatives = new ArrayList<>();
        for (int which = 0; which < 2; which++) {
            List<Entry> alternative = new ArrayList<>();
            int size = 1 + random.nextInt(2);
            for (int each = 0; each < size; each++) {
                alternative.add(depth > 0 && random.nextInt(4) == 0
                        ? someChoice(random, made, depth - 1) : someAsk(random));
            }
            alternatives.add(alternative);
        }
        Choice out = new Choice(alternatives);
        made.add(out);
        return out;
    }

    /** How many places choices stand at in {@code entries}, nested ones among them. */
    private static int placesIn(List<Entry> entries) {
        int out = 0;
        for (Entry each : entries) {
            if (each instanceof Choice choice) {
                out++;
                for (List<Entry> alternative : choice.alternatives()) {
                    out += placesIn(alternative);
                }
            }
        }
        return out;
    }

    /** How many alternatives the conditions {@code made} have, each condition once. */
    private static int owedIn(List<Choice> made) {
        int out = 0;
        for (Choice each : new HashSet<>(made)) {
            out += each.alternatives().size();
        }
        return out;
    }

    /** Two conditions on two positions, every combination within the figure: each of them,
     *  since a row past both is along one. */
    @Test
    void conditionsOnPositionsApartWithinTheFigureAreEveryCombination() {
        Choice onX = oneOf(ask(X, 1), ask(X, 2), ask(X, 3));
        Choice onY = oneOf(ask(Y, 1), ask(Y, 2), ask(Y, 3));
        Walked.Open<Entry, TermPath> walked = open(walked(onX, onY));

        assertTrue(walked.everyWay(), () -> "every way a row takes: " + walked);
        List<List<Entry>> every = new ArrayList<>();
        for (int x = 1; x <= 3; x++) {
            for (int y = 1; y <= 3; y++) {
                every.add(List.of(ask(X, x), ask(Y, y)));
            }
        }
        assertEquals(every, chosen(walked));
    }

    /**
     * Two conditions on two positions whose combinations are more than the figure: each
     * alternative once, beside the other's first, the second alternatives of both before the
     * third of either — and the figure, since a row may be along a combination left out.
     */
    @Test
    void conditionsOnPositionsApartPastTheFigureAreEachAlternativeOnceAndTheFigure() {
        List<Entry> onX = new ArrayList<>();
        List<Entry> onY = new ArrayList<>();
        for (int each = 1; each <= 5; each++) {
            onX.add(ask(X, each));
            onY.add(ask(Y, each));
        }
        Walked.Open<Entry, TermPath> walked = open(walked(oneOf(onX.toArray(Entry[]::new)),
                oneOf(onY.toArray(Entry[]::new))));

        assertFalse(walked.everyWay(), () -> "not every way a row takes: " + walked);
        assertEquals(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG, walked.stoppedBy());
        List<List<Entry>> each = new ArrayList<>();
        each.add(List.of(ask(X, 1), ask(Y, 1)));
        for (int number = 2; number <= 5; number++) {
            each.add(List.of(ask(X, number), ask(Y, 1)));
            each.add(List.of(ask(X, 1), ask(Y, number)));
        }
        assertEquals(each, chosen(walked));
    }

    /** Two conditions on one position are walked together, and a way they close is left out. */
    @Test
    void conditionsOnOnePositionAreTakenTogether() {
        Walked.Open<Entry, TermPath> walked = open(walked(oneOf(ask(X, 1), ask(X, 2)),
                oneOf(ask(X, 2), ask(X, 3))));

        assertEquals(List.of(List.of(ask(X, 2), ask(X, 2))), chosen(walked));
        assertTrue(walked.everyWay());
    }

    /**
     * Where every alternative of one group closes against what is asked beside it, nothing is
     * past the whole — whatever another group leaves open — and the way that closed first says
     * why.
     */
    @Test
    void aGroupWalkedToItsEndAndClosedClosesTheWhole() {
        Walked<Entry, TermPath> walked = walked(ask(X, 0), oneOf(ask(Y, 1), ask(Y, 2)),
                oneOf(ask(X, 1), ask(X, 2)));

        assertEquals(new Walked.Closed<>(List.of(ask(X, 0), ask(X, 1)), X), walked,
                "what is asked beside the conditions, the first alternative that closed, and"
                        + " the position nothing was left at");
    }

    /** What is asked beside the choices is judged by the walk too, with no choice on the way. */
    @Test
    void whatIsAskedBesideTheChoicesClosesTheWayWithNoChoiceOnIt() {
        Walked<Entry, TermPath> walked = walked(ask(X, 0), ask(Y, 1), ask(X, 1));

        assertEquals(new Walked.Closed<>(List.of(ask(X, 0), ask(Y, 1), ask(X, 1)), X), walked);
    }

    /** A condition nested in an alternative is chosen where it stands. */
    @Test
    void aConditionInsideAnAlternativeIsChosenWhereItStands() {
        Choice inner = oneOf(ask(X, 1), ask(X, 2));
        Choice outer = new Choice(List.of(List.of(ask(X, 1, 2), inner), List.of(ask(X, 3))));
        Walked.Open<Entry, TermPath> walked = open(walked(outer, ask(Y, 0)));

        assertEquals(List.of(
                        List.of(ask(X, 1, 2), ask(X, 1), ask(Y, 0)),
                        List.of(ask(X, 1, 2), ask(X, 2), ask(Y, 0)),
                        List.of(ask(X, 3), ask(Y, 0))),
                chosen(walked));
    }

    /**
     * A choice nested in an alternative is chosen where it stands however the vocabulary hands
     * the alternatives over — a vocabulary making them afresh each time it is asked included,
     * which hands back an entry equal to the one chosen and never the same one.
     */
    @Test
    void aNestedChoiceIsKeptWhereTheAlternativesAreMadeAfresh() {
        Choice inner = oneOf(ask(X, 1), ask(X, 2));
        Choice outer = new Choice(List.of(List.of(ask(X, 1, 2), inner), List.of(ask(X, 3))));
        Walked.Open<Entry, TermPath> walked = open(OneOfEach.walk(List.of(outer, ask(Y, 0)),
                AFRESH, CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT,
                CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG));

        assertEquals(List.of(
                        List.of(ask(X, 1, 2), ask(X, 1), ask(Y, 0)),
                        List.of(ask(X, 1, 2), ask(X, 2), ask(Y, 0)),
                        List.of(ask(X, 3), ask(Y, 0))),
                chosen(walked), "the nested choice's alternative is in each way past it");
    }

    /**
     * Where the looking one group did leaves none for the next, the ways the first found are
     * handed on — not no way at all — with the choice of the one not looked at left as it
     * stands, said to be left, and the figure that left it unlooked at.
     */
    @Test
    void aGroupLeftNothingToLookWithLeavesTheWaysBeforeIt() {
        List<Entry> entries = new ArrayList<>();
        int most = CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT.maximum();
        // Every alternative of the first is looked at, and only the last of them is open.
        entries.add(ask(X, most - 1));
        List<Entry> alternatives = new ArrayList<>();
        for (int each = 0; each < most; each++) {
            alternatives.add(ask(X, each));
        }
        entries.add(oneOf(alternatives.toArray(Entry[]::new)));
        Choice onY = oneOf(ask(Y, 1), ask(Y, 2));
        entries.add(onY);
        Walked.Open<Entry, TermPath> walked = open(walked(entries.toArray(Entry[]::new)));

        assertEquals(List.of(new OneOfEach.Way.LeftUnchosen<>(
                        List.of(ask(X, most - 1), ask(X, most - 1)), List.of(onY))), walked.ways(),
                "the open way of the first, with the choice not looked at left as it stands");
        assertEquals(CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT, walked.stoppedBy());
    }

    /** {@link #VALUES}, handing the alternatives of a choice over as new entries each time. */
    private static final OneOfEach.Vocabulary<Entry, Map<TermPath, Set<Integer>>, TermPath>
            AFRESH = new OneOfEach.Vocabulary<>() {

                @Override
                public List<List<Entry>> alternatives(Entry entry) {
                    List<List<Entry>> asked = VALUES.alternatives(entry);
                    return asked == null ? null : asked.stream()
                            .map(way -> way.stream().map(each -> afresh(each)).toList())
                            .toList();
                }

                @Override
                public Set<TermPath> positions(Entry entry) {
                    return VALUES.positions(entry);
                }

                @Override
                public Map<TermPath, Set<Integer>> nothing() {
                    return VALUES.nothing();
                }

                @Override
                public Step<Map<TermPath, Set<Integer>>, TermPath> with(
                        Map<TermPath, Set<Integer>> so, Entry entry) {
                    return VALUES.with(so, entry);
                }
            };

    /** An entry equal to {@code entry} and not the same one. */
    private static Entry afresh(Entry entry) {
        return switch (entry) {
            case Ask(TermPath at, Set<Integer> values) -> new Ask(at, values);
            case Choice(List<List<Entry>> alternatives) -> new Choice(alternatives);
            case Hashed(List<List<Entry>> alternatives, AtomicInteger hashed) ->
                    new Hashed(alternatives, hashed);
        };
    }

    /** More open ways than are looked along: the first of them, and the figure that cut them. */
    @Test
    void moreOpenWaysThanAreLookedAlongKeepTheFirstOnes() {
        int most = CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG.maximum();
        List<Entry> alternatives = new ArrayList<>();
        for (int each = 0; each <= most; each++) {
            alternatives.add(ask(X, each));
        }
        Walked.Open<Entry, TermPath> walked = open(walked(oneOf(
                alternatives.toArray(Entry[]::new))));

        assertEquals(most, walked.ways().size());
        assertEquals(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG, walked.stoppedBy());
    }

    /**
     * More ways that hold together in one group than are looked along: every alternative of
     * every choice is still in a way handed on. The ways the walk finds first differ only in the
     * choices it comes to last, so a way past the second alternative of the first choice, which
     * only the ways after those take, is the one a row at a border may need.
     */
    @Test
    void moreWaysInOneGroupThanAreLookedAlongStillTakeEachAlternativeOnce() {
        List<Entry> entries = new ArrayList<>();
        entries.add(oneOf(ask(X, 1), ask(X, 2)));
        for (int each = 0; each < 5; each++) {
            entries.add(oneOf(ask(X, 1, 2), ask(X, 1, 2, 10 + each)));
        }
        Walked.Open<Entry, TermPath> walked = open(walked(entries.toArray(Entry[]::new)));

        assertEquals(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG, walked.stoppedBy());
        List<List<Entry>> ways = chosen(walked);
        assertTrue(ways.size() <= CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG.maximum(),
                () -> "no more than the figure: " + ways.size());
        assertTrue(ways.stream().anyMatch(way -> way.getFirst().equals(ask(X, 1))),
                () -> "the first alternative of the first choice: " + ways);
        assertTrue(ways.stream().anyMatch(way -> way.getFirst().equals(ask(X, 2))),
                () -> "the second alternative of the first choice: " + ways);
        for (int each = 0; each < 5; each++) {
            Entry second = ask(X, 1, 2, 10 + each);
            assertTrue(ways.stream().anyMatch(way -> way.contains(second)),
                    () -> "the second alternative of a later choice, " + second + ": " + ways);
        }
    }

    /**
     * An alternative of a choice nested inside another is looked for through the alternative of
     * the outer choice that holds it. The ways the walk finds first all take the outer choice's
     * first alternative, which does not hold the inner choice, so a way taking the inner choice's
     * second alternative is one the outer choice's second alternative leads to.
     */
    @Test
    void anAlternativeOfANestedChoiceIsLookedForThroughTheAlternativeThatHoldsIt() {
        Choice inner = oneOf(ask(X, 1), ask(X, 2));
        Choice outer = new Choice(List.of(List.of(ask(X, 1, 2)), List.of(ask(X, 1, 2), inner)));
        List<Entry> entries = new ArrayList<>();
        entries.add(outer);
        for (int each = 0; each < 5; each++) {
            entries.add(oneOf(ask(X, 1, 2), ask(X, 1, 2, 10 + each)));
        }
        Walked.Open<Entry, TermPath> walked = open(walked(entries.toArray(Entry[]::new)));

        List<List<Entry>> ways = chosen(walked);
        assertTrue(ways.stream().anyMatch(way -> way.contains(ask(X, 1))),
                () -> "the inner choice's first alternative: " + ways);
        assertTrue(ways.stream().anyMatch(way -> way.contains(ask(X, 2))),
                () -> "the inner choice's second alternative: " + ways);
        assertEquals(ways.size(), new HashSet<>(ways).size(), () -> "no way twice: " + ways);
    }

    /**
     * Where a choice's alternatives are more than the figure lets through, the later ones are
     * the ones left: no choice's alternative is passed over for another's, and the figure says
     * that the rest was not looked at.
     */
    @Test
    void pastTheFigureNoAlternativeIsPassedOverForALaterOne() {
        int limit = CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG.maximum();
        List<Entry> alternatives = new ArrayList<>();
        for (int each = 0; each <= limit; each++) {
            alternatives.add(ask(X, each));
        }
        Walked.Open<Entry, TermPath> walked = open(walked(oneOf(
                alternatives.toArray(Entry[]::new))));

        List<List<Entry>> ways = chosen(walked);
        assertEquals(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG, walked.stoppedBy());
        assertEquals(limit, ways.size());
        assertEquals(alternatives.subList(0, limit),
                ways.stream().map(List::getFirst).toList());
    }

    /**
     * A choice nested in the third alternative of another is not met until that alternative is
     * looked for, which is after the second alternative of every choice met before it: its own
     * second alternative is still owed a way.
     */
    @Test
    void aNestedChoiceMetAtTheThirdAlternativeGetsBothOfItsAlternatives() {
        Choice inner = oneOf(ask(X, 1), ask(X, 2));
        Choice outer = new Choice(List.of(List.of(ask(X, 1, 2)), List.of(ask(X, 1, 2)),
                List.of(ask(X, 1, 2), inner)));
        List<Entry> entries = new ArrayList<>();
        entries.add(outer);
        for (int each = 0; each < 4; each++) {
            entries.add(oneOf(ask(X, 1, 2), ask(X, 1, 2, 10 + each)));
        }
        Walked.Open<Entry, TermPath> walked = open(walked(entries.toArray(Entry[]::new)));

        List<List<Entry>> ways = chosen(walked);
        assertTrue(ways.stream().anyMatch(way -> way.contains(ask(X, 1))),
                () -> "the inner choice's first alternative: " + ways);
        assertTrue(ways.stream().anyMatch(way -> way.contains(ask(X, 2))),
                () -> "the inner choice's second alternative: " + ways);
    }

    /**
     * Independent groups whose ways are more than the figure let through together: the second
     * alternative of the small group is not passed over for the later alternatives of the large
     * one, as it is not within a group.
     */
    @Test
    void anAlternativeOfASmallGroupIsNotPassedOverForTheLaterOnesOfALargeGroup() {
        int limit = CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG.maximum();
        List<Entry> alternatives = new ArrayList<>();
        for (int each = 0; each <= limit; each++) {
            alternatives.add(ask(X, each));
        }
        Walked.Open<Entry, TermPath> walked = open(walked(
                oneOf(alternatives.toArray(Entry[]::new)), oneOf(ask(Y, 1), ask(Y, 2))));

        List<List<Entry>> ways = chosen(walked);
        assertEquals(limit, ways.size());
        assertTrue(ways.stream().anyMatch(way -> way.contains(ask(Y, 1))), () -> "y 1: " + ways);
        assertTrue(ways.stream().anyMatch(way -> way.contains(ask(Y, 2))), () -> "y 2: " + ways);
        assertTrue(ways.stream().anyMatch(way -> way.contains(ask(X, 1))), () -> "x 1: " + ways);
    }

    /**
     * Choices turning on one position whose ways are far more than the figure: the first way,
     * then the second alternative of each choice beside the first of every other, the choices in
     * the order the walk came to them and no more than the figure.
     */
    @Test
    void manyChoicesGetTheirSecondAlternativeOneBesideTheFirstsInTheOrderTheyAreMet() {
        int limit = CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG.maximum();
        List<Entry> entries = new ArrayList<>();
        for (int each = 0; each < limit + 4; each++) {
            entries.add(oneOf(ask(X, 1, 2), ask(X, 1, 2, 10 + each)));
        }
        Walked.Open<Entry, TermPath> walked = open(walked(entries.toArray(Entry[]::new)));

        List<List<Entry>> ways = chosen(walked);
        assertEquals(limit, ways.size());
        for (int way = 0; way < limit; way++) {
            List<Entry> expected = new ArrayList<>();
            for (int each = 0; each < entries.size(); each++) {
                expected.add(way > 0 && each == way - 1 ? ask(X, 1, 2, 10 + each) : ask(X, 1, 2));
            }
            assertEquals(expected, ways.get(way), "way " + way);
        }
    }

    /**
     * What is done to give every alternative a way does not take the looking a later group is
     * owed: the group on another position is looked at whole, however much the first group's
     * alternatives were looked for.
     */
    @Test
    void lookingForTheAlternativesOfOneGroupLeavesTheLookingOfTheNextGroup() {
        List<Entry> entries = new ArrayList<>();
        int choices = CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT.maximum() / 8;
        for (int each = 0; each < choices; each++) {
            entries.add(oneOf(ask(X, 1, 2), ask(X, 1, 2, 10 + each)));
        }
        Choice onY = oneOf(ask(Y, 1), ask(Y, 2));
        entries.add(onY);
        Walked.Open<Entry, TermPath> walked = open(walked(entries.toArray(Entry[]::new)));

        assertFalse(walked.ways().isEmpty());
        for (OneOfEach.Way<Entry> way : walked.ways()) {
            assertInstanceOf(OneOfEach.Way.Chosen.class, way,
                    () -> "the choice on y is chosen in every way: " + way);
        }
    }

    /**
     * Whatever the shape of the groups and the choices, the ways handed on are no more than the
     * figure and none twice, the first way is the one that takes every first alternative, and the
     * alternatives are not passed over for one another: for every number up to which the
     * alternatives of all the choices, one way each beside the firsts, fit in the figure, every
     * alternative up to that number has a way.
     *
     * <p>Over every shape of three choices with up to nine alternatives each, on one position and
     * on two, so that the shapes where the ways are more than the figure and the ones where they
     * are fewer are both there.
     */
    @Test
    void whateverTheShapeTheWaysAreWithinTheFigureOnceAndFairToTheAlternatives() {
        int limit = CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG.maximum();
        for (int onTwo = 0; onTwo < 2; onTwo++) {
            for (int a = 1; a <= 9; a++) {
                for (int b = 1; b <= 9; b++) {
                    for (int c = 1; c <= 9; c++) {
                        int[] sizes = {a, b, c};
                        TermPath[] ats = {X, onTwo == 1 ? Y : X, X};
                        int[] froms = {10, 110, 210};
                        List<Entry> entries = new ArrayList<>();
                        for (int each = 0; each < 3; each++) {
                            entries.add(alternativesOn(ats[each], froms[each], sizes[each]));
                        }
                        String shape = Arrays.toString(sizes) + (onTwo == 1 ? " on two" : " on one");
                        List<List<Entry>> ways = chosen(open(walked(entries.toArray(Entry[]::new))));

                        assertTrue(ways.size() <= limit, shape + ": no more than the figure");
                        assertEquals(ways.size(), new HashSet<>(ways).size(),
                                shape + ": no way twice");
                        assertEquals(List.of(ask(ats[0], 1, 2, froms[0]),
                                        ask(ats[1], 1, 2, froms[1]), ask(ats[2], 1, 2, froms[2])),
                                ways.getFirst(), shape + ": the first way takes every first");
                        for (int number = 1; number < 9; number++) {
                            int owed = 1;
                            for (int size : sizes) {
                                owed += Math.min(size - 1, number);
                            }
                            if (owed > limit) {
                                break;
                            }
                            for (int each = 0; each < 3; each++) {
                                for (int alternative = 1;
                                        alternative <= Math.min(sizes[each] - 1, number);
                                        alternative++) {
                                    Entry wanted = ask(ats[each], 1, 2, froms[each] + alternative);
                                    assertTrue(ways.stream().anyMatch(way -> way.contains(wanted)),
                                            shape + ": " + wanted + " has a way");
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    /** A choice of {@code count} alternatives, each asking {@code at} to be 1 or 2 or a value of
     *  its own, from {@code from} up. Any alternatives of choices on one position hold together. */
    private static Choice alternativesOn(TermPath at, int from, int count) {
        List<Entry> out = new ArrayList<>();
        for (int each = 0; each < count; each++) {
            out.add(ask(at, 1, 2, from + each));
        }
        return oneOf(out.toArray(Entry[]::new));
    }

    /**
     * A walk the figure stopped before a group was looked at to its end proves nothing, however
     * many of its ways closed.
     */
    @Test
    void aWalkTheFigureStoppedProvesNothing() {
        List<Entry> entries = new ArrayList<>();
        int choices = Integer.numberOfTrailingZeros(Integer.highestOneBit(
                CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT.maximum()));
        for (int each = 0; each < choices; each++) {
            entries.add(oneOf(ask(X, 0, 1), ask(X, 0, 1, 2)));
        }
        entries.add(oneOf(ask(X, 5), ask(X, 6)));

        assertEquals(new Walked.Stopped<Entry, TermPath>(
                        CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT),
                walked(entries.toArray(Entry[]::new)), "nothing proved and no way found");
    }

    /** A way with no choice on it that holds together is the one way, and every way. */
    @Test
    void aWayWithNoChoiceIsTheOneWay() {
        Walked.Open<Entry, TermPath> walked = open(walked(ask(X, 0), ask(Y, 1)));

        assertEquals(List.of(List.of(ask(X, 0), ask(Y, 1))), chosen(walked));
        assertNull(walked.stoppedBy());
    }
}
