package souther.compiler.query;

import souther.compiler.conformance.ConformanceCorpus;
import org.junit.jupiter.api.Test;

import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Two stores given the same sources are asked the same questions and answer them the same.
 *
 * <p>What an edit costs rests on an answer that means what the last one meant coming out equal to
 * it. That is a property of the answers and not of the engine, and nothing else here can see it
 * fail: a value that compares by identity leaves every check green and every reader of it running
 * again forever. So it is asked of two compilations of one input, where anything that compares by
 * where it came from has to say no.
 *
 * <p>Two things are asked at once and told apart. An answer that is the same thing said twice and
 * compares unequal anyway is a value that is not one — an array, or something holding a way of
 * reading a store. An answer that says something different is a compile that did not reproduce,
 * which is a different fault with the same symptom, and there is no reason for one of those to
 * exist at all.
 *
 * <p>What it sees is what the corpora reach. An answer no question about them asks for is not
 * compared here, and what the corpora reach is
 * {@code AConformanceCorpusReachesEveryConstructTheLanguageDeclaresTest}'s to say.
 *
 * <p>What is known and not fixed is written out below by what causes it, not by which question it
 * reaches. A cause is one thing to fix; the questions it arrives at are however many happen to read
 * it today, and restructuring what an answer holds would rewrite that list without changing what is
 * wrong. Exactly the causes below, so fixing one is a failure until it is struck off, and so is
 * adding one.
 */
class EquivalentDatabasesAnswerTheSameTest {

    /**
     * A thing kept in an answer that cannot compare as a value, the questions it is reached from,
     * and where it is being dealt with.
     *
     * <p>The questions and not the paths. A cause is one thing to fix wherever it turns up, so
     * moving what an answer holds around inside itself is not news; a cause turning up under a
     * question that did not have it is a new place the debt has reached, and that is. Which is what
     * makes this a register and not a list of what to overlook: putting a {@code byte[]} in some new
     * answer fails here, and the line to add says which of the two things it has to become.
     *
     * <p>Two ways out and no third. Something that says what it is becomes a value — that is
     * {@code byte[]}, which means what its bytes mean and is compared as an address. Something that
     * does something is a capability, and a capability is built where it is used and never answered
     * with. Which of the two each of these is is written here because it is the fix, and a note
     * saying only that it is known would leave the next reader to decide it again.
     */
    private record Known(String cause, Set<String> asked, String fix) {}

    private static final List<Known> KNOWN = List.of(
            new Known("byte[]",
                    Set.of("All", "Classes", "Linked", "Evaluated", "EvaluationLinked"),
                    "a value: what a class is is its bytes, so a wrapper comparing them is what "
                            + "lets a module whose classes came out the same leave its readers "
                            + "alone. Five questions and one thing to fix"),
            new Known("souther.compiler.query.Db",
                    Set.of("ModuleScope"),
                    "a capability: Scoping.Scoped carries a way of asking the modules around this "
                            + "one a further question, and it holds this store to ask with. Where "
                            + "a scope has been taken apart already, that is the half of the "
                            + "assembly nobody has yet — it belongs inside the compute that asks"),
            new Known("souther.compiler.inputs.InputDomain",
                    Set.of("Inputs"),
                    "unclassified: whether it is something that says what it is or something that "
                            + "does something has to be read before it is either, so the fix is to "
                            + "read it"),
            new Known("souther.compiler.query.Bodies$Elaborated",
                    Set.of("Checked"),
                    "unclassified: as above"));

    /**
     * And they are asked the same questions. What an answer was built from is what an edit is
     * absorbed by, so which questions a compile reaches is as much what it did as what it said: two
     * stores over one input reaching different graphs would mean the dependencies recorded in one
     * are not the ones the other would keep.
     *
     * <p>Its own sentence rather than a line of the one below, which is about what the two kept
     * where they were asked the same thing.
     */
    @Test
    void bothStoresAreAskedTheSameQuestions() {
        for (ConformanceCorpus corpus : ConformanceCorpus.all()) {
            Set<Key<?>> one = corpus.analyse().compilation().db().everyAnswer().keySet();
            Set<Key<?>> other = corpus.analyse().compilation().db().everyAnswer().keySet();
            Set<String> onlyOne = new TreeSet<>();
            one.stream().filter(key -> !other.contains(key)).forEach(key -> onlyOne.add(key.toString()));
            Set<String> onlyOther = new TreeSet<>();
            other.stream().filter(key -> !one.contains(key)).forEach(key -> onlyOther.add(key.toString()));
            assertEquals(Set.of(), onlyOne, "asked only the first time, of " + corpus);
            assertEquals(Set.of(), onlyOther, "asked only the second time, of " + corpus);
        }
    }

    @Test
    void everyAnswerMeansTheSameThingInBothStores() {
        Map<String, Set<String>> sameThingTwice = new TreeMap<>();
        Map<String, Set<String>> differentThings = new TreeMap<>();
        Map<String, Set<String>> where = new TreeMap<>();
        for (ConformanceCorpus corpus : ConformanceCorpus.all()) {
            Map<Key<?>, Answer<?>> one = corpus.analyse().compilation().db().everyAnswer();
            Map<Key<?>, Answer<?>> other = corpus.analyse().compilation().db().everyAnswer();
            Set<Key<?>> asked = new HashSet<>(one.keySet());
            asked.retainAll(other.keySet());
            for (Key<?> key : asked) {
                Answer<?> a = one.get(key);
                Answer<?> b = other.get(key);
                if (a.equals(b)) {
                    continue;
                }
                for (Divergence each : Divergence.between(a, b)) {
                    Map<String, Set<String>> into =
                            each.kind() == Divergence.Kind.THE_SAME_THING_TWICE
                                    ? sameThingTwice : differentThings;
                    into.computeIfAbsent(each.cause(), _ -> new TreeSet<>())
                            .add(key.getClass().getSimpleName());
                    where.computeIfAbsent(each.cause(), _ -> new TreeSet<>())
                            .add(key.getClass().getSimpleName() + each.path());
                }
            }
        }

        assertEquals(Map.of(), differentThings,
                "one input compiled twice answered two different things, which no equality can fix");
        Map<String, Set<String>> known = new TreeMap<>();
        KNOWN.forEach(each -> known.put(each.cause(), new TreeSet<>(each.asked())));
        assertEquals(known, sameThingTwice,
                "what is kept in an answer and cannot compare as a value, by the questions it is "
                        + "reached from. Found at " + where);
    }
}
