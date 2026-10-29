package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.Case;
import souther.compiler.inputs.CasesLeft;
import souther.compiler.inputs.Refinement;
import souther.compiler.inputs.TermPath;
import souther.compiler.types.LanguageCaseId;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A place {@link WhereARunReachingARelationStands} leaves out is one no run that reaches the
 * relation stands at, whichever row the run is in.
 *
 * <p>The answer is held against a count that shares nothing with it: every way a row can be, over
 * the cases of the sums the paths go through and over which elements a path under an element
 * stands at. A place is stood at by some run where there is a row, and a choice of an element for
 * each element step of each path, in which every place read and the place asked are in the cases
 * they narrow to. The class answers false only where there is none; and over paths with no
 * element or key it answers false exactly there, so that what it leaves in is a place some row
 * has and not a place it did not manage to rule out.
 */
class AnOperationLeftOutOfARunThatReachesARelationIsWorkedOutByNoSuchRunTest {

    private static Refinement caseOf(LanguageCaseId id) {
        return Refinement.of(new Case.SumCase(new TypeSymbol.LanguageCase(id), true));
    }

    /** Four cases of a sum, none of which is another. */
    private static final Refinement[] CASE = {
        caseOf(LanguageCaseId.DIVISION_BY_ZERO), caseOf(LanguageCaseId.NOT_WHOLE),
        caseOf(LanguageCaseId.NOT_A_NUMBER), caseOf(LanguageCaseId.NOT_A_DATE)};

    private static final CasesLeft[] NARROWINGS = {
        CasesLeft.of(CASE[0]), CasesLeft.of(CASE[1]), CasesLeft.of(CASE[2]),
        CasesLeft.ofEach(List.of(CASE[0], CASE[1])), CasesLeft.ofEach(List.of(CASE[1], CASE[2])),
        CasesLeft.ofEach(List.of(CASE[0], CASE[3]))};

    /** Which element of a list a step under it stands at: a row holds two. */
    private static final int ELEMENTS = 2;

    private static TermPath extended(TermPath path, int step) {
        return switch (step) {
            case 0 -> path.then("a");
            case 1 -> path.then("b");
            case 2 -> path.element();
            case 3 -> path.key();
            default -> path.refine(NARROWINGS[step - 4]);
        };
    }

    private static final int STEPS = 4 + NARROWINGS.length;

    /** Every path of up to {@code depth} steps under each of two roots. */
    private static List<TermPath> paths(int depth, boolean withElements) {
        List<TermPath> out = new ArrayList<>();
        for (String head : List.of("x", "y")) {
            List<TermPath> level = List.of(TermPath.of(head));
            out.addAll(level);
            for (int at = 0; at < depth; at++) {
                List<TermPath> next = new ArrayList<>();
                for (TermPath each : level) {
                    for (int step = 0; step < STEPS; step++) {
                        if (!withElements && (step == 2 || step == 3)) {
                            continue;
                        }
                        next.add(extended(each, step));
                    }
                }
                out.addAll(next);
                level = next;
            }
        }
        return out;
    }

    /**
     * What a path asks of a row for one choice of the elements its element steps stand at: for
     * each sum value it goes through, the cases it must be in. A sum value is named by the path
     * to it with the elements chosen.
     */
    private static List<Map<String, Set<Refinement>>> askedOfARow(TermPath path) {
        List<Map<String, Set<Refinement>>> out = new ArrayList<>();
        int unders = (int) path.steps().stream().filter(step ->
                step instanceof TermPath.Step.Element || step instanceof TermPath.Step.Key).count();
        int choices = 1;
        for (int i = 0; i < unders; i++) {
            choices *= ELEMENTS;
        }
        for (int choice = 0; choice < choices; choice++) {
            Map<String, Set<Refinement>> asked = new HashMap<>();
            StringBuilder value = new StringBuilder(path.head());
            int rest = choice;
            for (TermPath.Step step : path.steps()) {
                if (step instanceof TermPath.Step.Refine(var cases)) {
                    // Narrowed twice, a value is in the cases of both.
                    asked.merge(value.toString(), new HashSet<>(cases.atoms()), (had, now) -> {
                        had.retainAll(now);
                        return had;
                    });
                    // What is under a case is the payload of that case, and no other case's.
                    value.append("@").append(cases.atoms().stream().map(Refinement::spelled)
                            .sorted().toList());
                } else if (step instanceof TermPath.Step.Element
                        || step instanceof TermPath.Step.Key) {
                    value.append(step instanceof TermPath.Step.Key ? "{" : "[")
                            .append(rest % ELEMENTS).append("]");
                    rest /= ELEMENTS;
                } else {
                    value.append(".").append(step);
                }
            }
            // A path narrowed to no case at a value is stood at by no row.
            if (asked.values().stream().noneMatch(Set::isEmpty)) {
                out.add(asked);
            }
        }
        return out;
    }

    /** Whether some row has every one of {@code paths} stood at, each by some choice of its
     *  elements. */
    private static boolean someRowHasThemAll(List<TermPath> paths) {
        return someRowHasThemAll(paths, 0, new HashMap<>());
    }

    private static boolean someRowHasThemAll(List<TermPath> paths, int at,
                                             Map<String, Set<Refinement>> cases) {
        if (at == paths.size()) {
            return true;
        }
        for (Map<String, Set<Refinement>> asked : askedOfARow(paths.get(at))) {
            Map<String, Set<Refinement>> both = new HashMap<>(cases);
            boolean fits = true;
            for (Map.Entry<String, Set<Refinement>> each : asked.entrySet()) {
                Set<Refinement> now = new HashSet<>(each.getValue());
                if (both.containsKey(each.getKey())) {
                    now.retainAll(both.get(each.getKey()));
                }
                if (now.isEmpty()) {
                    fits = false;
                    break;
                }
                both.put(each.getKey(), now);
            }
            if (fits && someRowHasThemAll(paths, at + 1, both)) {
                return true;
            }
        }
        return false;
    }

    @Test
    void aPlaceLeftOutIsOneNoRowHasAlongsideThePlacesRead() {
        List<TermPath> pool = paths(3, true);
        Random random = new Random(2769);
        int leftOut = 0;
        for (int round = 0; round < 40_000; round++) {
            List<TermPath> reads = new ArrayList<>();
            int count = 1 + random.nextInt(3);
            for (int at = 0; at < count; at++) {
                reads.add(pool.get(random.nextInt(pool.size())));
            }
            TermPath place = pool.get(random.nextInt(pool.size()));
            List<TermPath> all = new ArrayList<>(reads);
            all.add(place);
            if (!new WhereARunReachingARelationStands(reads).mayStandAt(place)) {
                leftOut++;
                // Left out where the reads do not agree is a row no run has, and a relation never
                // reached is not what is decided here; nothing is left out then.
                assertTrue(someRowHasThemAll(reads), () -> "the reads agree: " + reads);
                assertFalse(someRowHasThemAll(all),
                        () -> "a row has " + place + " beside " + reads);
            }
        }
        assertTrue(leftOut > 1_000, "places were left out: " + leftOut);
    }

    @Test
    void overPathsWithNoElementAPlaceIsLeftOutExactlyWhereNoRowHasItBesideTheReads() {
        List<TermPath> pool = paths(3, false);
        Random random = new Random(2770);
        int left = 0;
        for (int round = 0; round < 40_000; round++) {
            List<TermPath> reads = new ArrayList<>();
            int count = 1 + random.nextInt(3);
            for (int at = 0; at < count; at++) {
                reads.add(pool.get(random.nextInt(pool.size())));
            }
            TermPath place = pool.get(random.nextInt(pool.size()));
            List<TermPath> all = new ArrayList<>(reads);
            all.add(place);
            if (!someRowHasThemAll(reads)) {
                assertTrue(new WhereARunReachingARelationStands(reads).mayStandAt(place),
                        () -> "nothing is left out of reads that do not agree: " + reads);
                continue;
            }
            left++;
            assertEquals(someRowHasThemAll(all),
                    new WhereARunReachingARelationStands(reads).mayStandAt(place),
                    () -> place + " beside " + reads);
        }
        assertTrue(left > 5_000, "reads that agree were asked: " + left);
    }

    /** Two elements of one list are two values, one in each case: a closure applied to every
     *  element stands at both. */
    @Test
    void underAnElementThePlacesOfApartCasesAreNotOneValue() {
        TermPath one = TermPath.of("contacts").element().then("reach").refine(CASE[0]);
        TermPath other = TermPath.of("contacts").element().then("reach").refine(CASE[1]);
        assertTrue(new WhereARunReachingARelationStands(List.of(one.then("email")))
                .mayStandAt(other.then("email")));
        assertTrue(someRowHasThemAll(List.of(one.then("email"), other.then("email"))));
    }

    /** One value of the row, so a closure applied to the element is in one case only. */
    @Test
    void underFieldsAndCasesAlonePlacesOfApartCasesAreNotStoodAtTogether() {
        TermPath one = TermPath.of("lead").then("reach").refine(CASE[0]).then("email");
        TermPath other = TermPath.of("lead").then("reach").refine(CASE[1]).then("email");
        WhereARunReachingARelationStands reaching = new WhereARunReachingARelationStands(
                List.of(one));
        assertFalse(reaching.mayStandAt(other));
        assertTrue(reaching.mayStandAt(TermPath.of("lead").then("reach").refine(CASE[0])));
        assertFalse(someRowHasThemAll(List.of(one, other)));
    }

    /** A relation read at places in apart cases of one value is reached by no run, which is not
     *  said by leaving every place out. */
    @Test
    void readsThatDoNotAgreeLeaveNothingOut() {
        TermPath a = TermPath.of("lead").then("reach").refine(CASE[0]).then("email");
        TermPath b = TermPath.of("lead").then("reach").refine(CASE[1]).then("phone");
        WhereARunReachingARelationStands reaching = new WhereARunReachingARelationStands(
                List.of(a, b));
        assertTrue(reaching.mayStandAt(TermPath.of("lead").then("reach").refine(CASE[0])
                .then("other")));
        assertTrue(reaching.mayStandAt(TermPath.of("lead").then("reach").refine(CASE[1])
                .then("other")));
    }
}
