package souther.compiler.coverage;

import org.junit.jupiter.api.Tag;
import org.junit.jupiter.api.Test;

import souther.compiler.conformance.ConformanceCorpus;
import souther.compiler.core.Core;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A place in a body is named by the way down to it, so two walks of that body name it alike and no
 * two places take one name.
 *
 * <p>The two halves an address has to have. If two places could take one name, a number filed under
 * that name is about neither of them; if one place took two names in two walks, nothing said of it
 * by one walk reaches the other. Node identity has the first and not the second — it is what a
 * numbering used, and it is why two numberings of one module could never be held against each
 * other.
 *
 * <p>Asked of trees this compiler produced rather than of trees written here. What an address has to
 * survive is expansion and lowering: a helper spliced into two calls is two places that look alike
 * and stand in different slots, and that is the case the whole thing is for.
 */
@Tag("population")
class TwoWalksOfOneBodyNameItsPlacesAlikeTest {

    /** A helper spliced twice, so two places are equal trees standing in different slots. */
    private static final String SPLICED = """
            module demo

            let picked (n: Int): List<Int> = [ n | n >= 240, n <= 300 ]

            behavior over : (a: Int, b: Int) -> List<Int>
            let over (a, b) = picked(a) ++ picked(b)
            """;

    private static final String NESTED = """
            module demo

            let inner (n: Int): List<Int> = [ n | n >= 240 ]

            let outer (n: Int): List<Int> = inner(n) ++ inner(n)

            behavior over : (a: Int, b: Int) -> List<Int>
            let over (a, b) = outer(a) ++ outer(b)
            """;

    @Test
    void noTwoPlacesOfOneBodyTakeOneName() {
        int places = 0;
        for (Map.Entry<String, Core> body : everyBody()) {
            NodeAddresses addresses = NodeAddresses.of(body.getKey(), body.getValue());
            Map<NodeAddress, Core> byName = new LinkedHashMap<>();
            for (Map.Entry<Core, NodeAddress> each : addresses.all().entrySet()) {
                Core already = byName.put(each.getValue(), each.getKey());
                assertEquals(null, already,
                        () -> "two places of `" + body.getKey() + "` are called "
                                + each.getValue());
            }
            places += addresses.size();
        }
        assertTrue(places > 0, "no body was walked at all, so this says nothing");
    }

    @Test
    void twoCompilationsOfOneSourceNameItsPlacesAlike() {
        for (String source : List.of(SPLICED, NESTED)) {
            assertEquals(namesIn(source), namesIn(source),
                    "the places of a body do not move between two compiles of its source");
        }
    }

    /**
     * A helper spliced twice is two places, and the addresses say which slot each stands in.
     *
     * <p>The case node identity had and a citation did not: the copies are equal trees written at
     * one line, so what tells them apart is the way down to each. Here that is the left and the
     * right of the {@code ++} they were spliced into.
     */
    @Test
    void aSplicedHelperIsAsManyPlacesAsItWasSplicedInto() {
        List<String> conditions = namesIn(SPLICED).stream()
                .filter(each -> each.endsWith("/IfCondition"))
                .sorted().toList();

        assertEquals(List.of(
                        "over/BinaryLeft/LetBody/IfCondition",
                        "over/BinaryLeft/LetBody/IfThen/IfCondition",
                        "over/BinaryRight/LetBody/IfCondition",
                        "over/BinaryRight/LetBody/IfThen/IfCondition"),
                conditions,
                "two guards of one comprehension, spliced into each side of the `++`");
    }

    /**
     * How many ways lead to a place, over everything walked here.
     *
     * <p>What says whether the set an address holds is a set for a reason. A tree gives one way to
     * each place; a pass that shared a subtree gives several, and the count is what the sharing
     * actually is rather than what a reader guesses it might be. Written down because an address
     * holding every way is only worth the trouble while there are places with more than one.
     */
    @Test
    void theseAreTheWaysThatLeadToAPlace() {
        Map<Integer, Integer> byWays = new TreeMap<>();
        for (Map.Entry<String, Core> body : everyBody()) {
            NodeAddresses addresses = NodeAddresses.of(body.getKey(), body.getValue());
            addresses.all().values()
                    .forEach(at -> byWays.merge(at.occurrences().size(), 1, Integer::sum));
        }

        // The claim is that sharing happens at all, not how much of it there is: the count moves
        // with whatever the corpora are and with what the passes above leave shared, and pinning it
        // would make this a test of the corpora. What it must not become is a body where every
        // place has one way, because then a set is holding one thing everywhere and nothing here
        // says whether it needed to.
        assertTrue(byWays.keySet().stream().anyMatch(ways -> ways > 1),
                () -> "no place has more than one way to it, so nothing here shows why an address"
                        + " holds a set of them: " + byWays);
        assertEquals(1, byWays.keySet().stream().mapToInt(Integer::intValue).min().orElse(0),
                () -> "and most places have exactly one: " + byWays);
    }

    /** The addresses of every place of every body of {@code source}, as text, from a fresh
     *  compile. */
    private static Set<String> namesIn(String source) {
        Set<String> out = new LinkedHashSet<>();
        for (Map.Entry<String, Core> body : bodiesOf(List.of(List.of(source)))) {
            NodeAddresses.of(body.getKey(), body.getValue()).all().values()
                    .forEach(at -> out.add(at.toString()));
        }
        return out;
    }

    private static List<Map.Entry<String, Core>> everyBody() {
        List<List<String>> sources = new ArrayList<>();
        ConformanceCorpus.all().forEach(corpus -> sources.add(corpus.sources()));
        sources.add(List.of(SPLICED));
        sources.add(List.of(NESTED));
        return bodiesOf(sources);
    }

    private static List<Map.Entry<String, Core>> bodiesOf(List<List<String>> sources) {
        List<Map.Entry<String, Core>> out = new ArrayList<>();
        for (List<String> each : sources) {
            Compilation compilation = Compilation.ofSources(each, ModulePath.EMPTY);
            compilation.answerEverything();
            int before = out.size();
            for (String module : compilation.modules()) {
                Bodies.Elaborated checked =
                        compilation.db().ask(new Bodies.Checked(module)).value();
                if (checked != null) {
                    out.addAll(checked.behaviorBodies().entrySet());
                }
            }
            assertTrue(out.size() > before,
                    () -> "a source set compiled to no body at all: " + compilation.errors());
        }
        return out;
    }
}
