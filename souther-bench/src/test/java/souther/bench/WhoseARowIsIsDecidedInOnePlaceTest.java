package souther.bench;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Whose it is to write a row at a point is decided once, and read by two accounts and nobody else.
 *
 * <p>A border owes a row at up to four points, and two of them can be owed to the declarations that
 * drew the line rather than to the body carrying the type. Everything that measures a behavior,
 * counts what it covers, raises a finding about it or offers it a row has to know which of the two
 * it is holding — and while every one of them asked for itself, the one that forgot weighed a
 * behavior's row against another behavior having no rows and held a build undetermined about a line
 * the module's own account had settled.
 *
 * <p>So the question is asked where the point is made, and what comes out of it is one of two arms.
 * This holds the two halves of that: the classifier is called from one place, and the arms are read
 * only by the two accounts made from them. A third reader is a consumer deciding again.
 */
class WhoseARowIsIsDecidedInOnePlaceTest {

    private static final String ATTRIBUTION = "souther.compiler.partition.PointAttribution";

    /**
     * Every way the classifier or one of its arms is reached from outside, one at a time.
     *
     * <p>Two rules in one answer, because one list of what is reached holds both. The classifier is
     * called where the point is made and nowhere else: everything that settled a point has arrived
     * there, so asked earlier the answer would be about whichever contributor had arrived, and asked
     * later it would be asked by whoever wanted it. And an arm is named by the two accounts and by
     * nothing else, because naming one is deciding whose a row is — which the classifier already
     * did.
     *
     * <p>Which member of which arm, reached which way, and by whom. Folded to the methods that touch
     * an arm somehow, this rule is passed by writing {@code new TheDeclarations(...)} inside a method
     * that is already allowed to hold {@code TheDeclarations::and} — the set of names does not move,
     * and what the name of this rule says did not happen would have happened.
     *
     * <p>So the answer is spelled per member and per way of reaching it, and the whole of it is
     * compared: a reach nobody has written down is a reach nobody has thought about, whichever kind
     * it is.
     */
    @Test
    void everyWayAnArmIsReachedFromOutside() {
        assertEquals(new java.util.TreeMap<>(Map.of(
                        // Merging the owners of two readings of one point, which is the declarations'
                        // account folding what it was given. A reference rather than a call because
                        // it is handed to `Map.merge`.
                        ATTRIBUTION + "$TheDeclarations#and REFERS",
                        List.of("souther.compiler.query.BorderObligationPointAssessment#across"),
                        // Which of this module's declarations owe the point, which is the arm
                        // answering about itself rather than anybody deciding which arm it is.
                        ATTRIBUTION + "$TheDeclarations#ownersIn CALLS",
                        List.of("souther.compiler.query.Adequacy$DeclaredBorders#compute",
                                "souther.compiler.query.BorderObligationPointAssessment#across"),
                        // And the two accounts, each naming both arms because each answers for the
                        // whole question: a producer that named one of them would be a point whose
                        // arm neither account holds.
                        ATTRIBUTION + "$TheDeclarations#case NAMES", ACCOUNTS,
                        ATTRIBUTION + "$TheReading#case NAMES", ACCOUNTS,
                        // Two points of one line are compared as values, which is what a reading
                        // holds ({@code OwedPoint}).
                        ATTRIBUTION + "#equals CALLS",
                        List.of("souther.compiler.partition.OwedPoint#equals"),
                        // And the classifier itself, which the rule above is about.
                        ATTRIBUTION + "#of CALLS",
                        List.of("souther.compiler.partition.Border#owes"))),
                reachesFromOutside());
    }

    /** The two accounts made from what the classifier answered. */
    private static final List<String> ACCOUNTS = List.of(
            "souther.compiler.query.BorderObligationPointAssessment#across",
            "souther.compiler.query.OwedBoundaryPoint#across");

    /**
     * Every reach to the classifier or one of its arms from outside it, by what is reached and how.
     *
     * <p>Sites inside {@link souther.compiler.partition.PointAttribution} are left out: what an arm
     * does with itself — holding its own field, comparing itself, making itself in its own static
     * initialiser — is the value being a value, and a rule about who may reach it from elsewhere is
     * not about that.
     */
    private static java.util.SortedMap<String, List<String>> reachesFromOutside() {
        java.util.SortedMap<String, java.util.SortedSet<String>> found = new java.util.TreeMap<>();
        try {
            for (Compiled.Site site : Compiled.sites()) {
                if (!site.owner().startsWith(ATTRIBUTION) || site.from().startsWith(ATTRIBUTION)) {
                    continue;
                }
                found.computeIfAbsent(site.owner() + "#" + site.member() + " " + site.how(),
                                _ -> new java.util.TreeSet<>())
                        .add(site.from() + "#" + written(site.method()));
            }
        } catch (IOException e) {
            throw new AssertionError("the compiled classes were not readable", e);
        }
        java.util.SortedMap<String, List<String>> out = new java.util.TreeMap<>();
        found.forEach((what, where) -> out.put(what, List.copyOf(where)));
        return out;
    }

    /** The method as somebody wrote it: a lambda is named for the one that holds it. */
    private static String written(String method) {
        if (!method.startsWith("lambda$")) {
            return method;
        }
        String rest = method.substring("lambda$".length());
        return rest.substring(0, rest.lastIndexOf('$'));
    }
}
