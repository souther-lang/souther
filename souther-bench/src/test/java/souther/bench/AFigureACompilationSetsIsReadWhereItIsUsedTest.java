package souther.bench;

import org.junit.jupiter.api.Test;

import souther.compiler.meaning.WhyUnread;
import souther.compiler.partition.Allowances;
import souther.compiler.partition.CompositionBudget;

import java.io.InputStream;
import java.lang.classfile.ClassFile;
import java.lang.classfile.ClassModel;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A budget a compilation may hold to another figure ({@link Allowances#SETTABLE}) is asked for its
 * figure where the figure is used, and copied by no class into a constant of its own when the class
 * is loaded: a copy holds the figure declared for every compilation after, whatever one says.
 *
 * <p>Asked of the compiled code. A class whose initializer both reaches one of these budgets and
 * asks a budget for its figure is taken to copy it; the two together are what a copy compiles to,
 * and a class that reaches one to name it — in an order, or in the list of the settable ones —
 * asks no figure there.
 */
class AFigureACompilationSetsIsReadWhereItIsUsedTest {

    private static final String BUDGET = CompositionBudget.class.getName();

    /** What asks a budget for the figure the compilation asking holds it to. */
    private static final Set<String> ASKS_THE_FIGURE_IN_FORCE =
            Set.of("maximum", "reached", "reachedAShareOf");

    /**
     * No class, loaded, runs anything that asks a budget for the figure in force.
     *
     * <p>What is kept when a class is loaded is kept for every compilation after, so a figure asked
     * there is the one in force for whichever compilation loaded the class first, and held for the
     * rest. Not only the initializer's own code: a figure asked a call or two away — a helper that
     * reads it, a stop made where it is reached — is held as well, in a constant or in a table
     * nothing changes.
     *
     * <p>The budget itself is no such thing. A class holding {@code CompositionBudget.X} holds a
     * name, and what it asks of it where it is used is asked of the compilation using it; it is the
     * answer, kept past the compilation, that is wrong. So this follows what the initializer
     * runs, and not what it names.
     *
     * <p>Followed by name: a call is taken to run every method of the class it names under that
     * name, and a class used is taken to run its initializer. That over-reaches, which is what the
     * list below is for; it does not follow a call through an interface or a method an override
     * replaces, which no check over what the code names can.
     */
    private static Map<String, String> loadedRunningWhatAsks(Compiled.Reading reading) {
        Map<String, List<Compiled.Site>> doing = new TreeMap<>();
        Map<String, Set<String>> methodsNamed = new TreeMap<>();
        for (Compiled.Site site : reading.sites()) {
            doing.computeIfAbsent(site.at(), _ -> new ArrayList<>()).add(site);
            methodsNamed.computeIfAbsent(site.from() + "#" + site.method(), _ -> new TreeSet<>())
                    .add(site.at());
        }
        Set<String> settable = new TreeSet<>();
        Allowances.SETTABLE.forEach(each -> settable.add(each.name()));
        Set<String> asking = new TreeSet<>();
        Set<Compiled.Site> askedOfANamedOne = new HashSet<>();
        for (Compiled.StaticRead each : reading.staticReads()) {
            Compiled.Site taken = each.takenBy();
            if (each.read().owner().equals(BUDGET) && taken != null
                    && taken.owner().equals(BUDGET)
                    && ASKS_THE_FIGURE_IN_FORCE.contains(taken.member())) {
                askedOfANamedOne.add(taken);
                if (settable.contains(each.read().member())
                        && !each.read().from().equals(BUDGET)) {
                    asking.add(each.read().at());
                }
            }
        }
        Set<String> askingOfOneHandedIn = new TreeSet<>();
        for (Compiled.Site site : reading.sites()) {
            if (site.how() == Compiled.How.CALLS && site.owner().equals(BUDGET)
                    && ASKS_THE_FIGURE_IN_FORCE.contains(site.member())
                    && !site.from().equals(BUDGET) && !askedOfANamedOne.contains(site)) {
                askingOfOneHandedIn.add(site.at());
            }
        }
        assertFalse(asking.isEmpty(), "some place asks for a figure, or this reads no call of it");
        asking.addAll(askingOfOneHandedIn);

        Map<String, String> reaching = new TreeMap<>();
        for (String loading : doing.keySet()) {
            if (!loading.contains("#<clinit>")) {
                continue;
            }
            String found = firstAsking(loading, doing, methodsNamed, asking);
            if (found != null) {
                reaching.put(loading.substring(0, loading.indexOf('#')), found);
            }
        }
        return reaching;
    }

    @Test
    void noClassLoadedRunsWhatAsksTheFigureInForce() {
        Map<String, String> reaching = loadedRunningWhatAsks(new Compiled.Reading(
                Compiled.sites(), Compiled.invocations(), Compiled.staticReads()));

        Set<String> unsaid = new TreeSet<>(reaching.keySet());
        unsaid.removeAll(LOADING_MAY_ASK.keySet());
        assertEquals(List.of(), List.copyOf(unsaid),
                "these run, when they are loaded, what asks a budget for the figure in force, and"
                        + " would hold the one in force for whichever compilation loaded them"
                        + " first: " + reaching);
        Set<String> gone = new TreeSet<>(LOADING_MAY_ASK.keySet());
        gone.removeAll(reaching.keySet());
        assertEquals(List.of(), List.copyOf(gone), "these run nothing of the kind any more");
    }

    /**
     * What this finds is asked of two classes written for it, which hold a figure the two ways a
     * class can: a stop made when it is loaded, by a helper of another class that reads the figure
     * where the stop is made; and a figure read by a helper of its own. Neither is a call of
     * {@code maximum} in its own initializer, which is all the check said it found.
     */
    @Test
    void whatAClassHoldsOfTheFigureInForceIsFoundWhereverItIsRead() throws Exception {
        List<ClassModel> held = new ArrayList<>();
        for (Class<?> each : List.of(AStopMadeWhenLoaded.class, AFigureReadByAHelper.class)) {
            String file = each.getName().substring(each.getPackageName().length() + 1) + ".class";
            try (InputStream bytes = each.getResourceAsStream(file)) {
                held.add(ClassFile.of().parse(bytes.readAllBytes()));
            }
        }
        Compiled.Reading fixtures = Compiled.read(held);
        List<Compiled.Site> sites = new ArrayList<>(Compiled.sites());
        sites.addAll(fixtures.sites());
        List<Compiled.StaticRead> reads = new ArrayList<>(Compiled.staticReads());
        reads.addAll(fixtures.staticReads());

        Map<String, String> reaching = loadedRunningWhatAsks(
                new Compiled.Reading(sites, fixtures.invocations(), reads));

        assertTrue(reaching.containsKey(AStopMadeWhenLoaded.class.getName()), () -> reaching.toString());
        assertTrue(reaching.containsKey(AFigureReadByAHelper.class.getName()), () -> reaching.toString());
    }

    /** A stop made when the class is loaded, which holds the figure in force then. */
    static final class AStopMadeWhenLoaded {

        static final WhyUnread HELD = WhyUnread.pastTheReadings();
    }

    /** A figure read by a helper, and held. */
    static final class AFigureReadByAHelper {

        static final int HELD = readings();

        private static int readings() {
            return CompositionBudget.READINGS_OF_ONE_CONDITION.maximum();
        }
    }

    /**
     * What a class run when it is loaded may ask the figure in force of, and why it holds none of
     * what it is told.
     *
     * <p>Where a budget is handed to what asks it, this cannot tell which budget, and takes it to be
     * any; so these are read by what each says, and a settable budget handed where they ask would
     * not be seen here. A settable budget named where it is handed is.
     */
    private static final Map<String, String> LOADING_MAY_ASK = Map.of(
            "souther.compiler.partition.Generator$TellingArmsApart",
            "copies the rows a walk hands the choice of a row among"
                    + " (ROWS_A_WALK_HANDS_THE_CHOICE_OF_A_ROW), which no compilation may set",
            "souther.compiler.partition.Generator$ReachingWhatIsJudged",
            "copies the rows a walk hands the choice of a row among"
                    + " (ROWS_A_WALK_HANDS_THE_CHOICE_OF_A_ROW), which no compilation may set",
            "souther.compiler.check.FieldDomains",
            "makes a concluding, which counts to the parts a derivation concludes with"
                    + " (PARTS_A_DERIVATION_CONCLUDES), which no compilation may set",
            "souther.compiler.check.StringPredicates",
            "makes a concluding, which counts to the parts a derivation concludes with"
                    + " (PARTS_A_DERIVATION_CONCLUDES), which no compilation may set");

    /** The first method asking for a figure that {@code start} runs, or null where it runs none. */
    private static String firstAsking(String start, Map<String, List<Compiled.Site>> doing,
                                      Map<String, Set<String>> methodsNamed, Set<String> asking) {
        Set<String> seen = new TreeSet<>();
        Deque<String> next = new ArrayDeque<>();
        next.add(start);
        seen.add(start);
        while (!next.isEmpty()) {
            String method = next.poll();
            if (asking.contains(method)) {
                return method;
            }
            for (Compiled.Site site : doing.getOrDefault(method, List.of())) {
                if (site.how() == Compiled.How.ASKS || site.how() == Compiled.How.NAMES) {
                    continue;
                }
                List<String> runs = new ArrayList<>();
                runs.addAll(methodsNamed.getOrDefault(site.owner() + "#" + site.member(),
                        Set.of()));
                runs.addAll(methodsNamed.getOrDefault(site.owner() + "#<clinit>", Set.of()));
                for (String each : runs) {
                    if (seen.add(each)) {
                        next.add(each);
                    }
                }
            }
        }
        return null;
    }

    /**
     * What a budget is asked where it is read off at once and not handed on: a figure, or its
     * place among the budgets, which is what a switch over them compiles to.
     */
    private static final Set<String> READ_OFF = Set.of("reached", "maximum", "declared",
            "atDeclared", "ordinal");

    /**
     * The places that name a budget a compilation may set and hand on the budget itself, and why
     * none of them is a stop that would be told by the budget: each names it as one of the
     * budgets, not as something stopped at it.
     */
    private static final Map<String, String> NAMED_AS_A_BUDGET = Map.of(
            "souther.compiler.partition.Allowances#<clinit>()V",
            "the budgets a compilation may set, which this rule is about",
            "souther.compiler.publish.PublicationOrders#<clinit>()V",
            "the order the budgets are written out in",
            "souther.compiler.meaning.Proposition$SoManyHold#writtenOutForAReader()"
                    + "Lsouther/compiler/meaning/WhichOfThemHold$Written;",
            "hands the budget to the writing out of a count, which reads the figure and the"
                    + " figure a stop was at off it where it uses it");

    /**
     * A budget a compilation may set is read off where it is named: the figure it stopped at
     * ({@link CompositionBudget#reached}) or the figure it is held to, never the budget handed on
     * by itself. A stop that holds a budget by its kind and makes the figure when it is told says
     * the one in force then, which outside a compilation is the one declared; so a budget that may
     * be set reaches no such holder, whichever of them it is, because nothing hands it on.
     *
     * <p>Asked of the compiled code, where naming a budget is reading its constant, and what is
     * done with it is the next instruction. A place that hands it on as one of the budgets — an
     * order, the list of the settable ones — says so here, and is no stop.
     */
    @Test
    void aBudgetACompilationMaySetIsReadOffWhereItIsNamed() {
        Set<String> settable = new TreeSet<>();
        Allowances.SETTABLE.forEach(each -> settable.add(each.name()));
        Set<String> handedOn = new TreeSet<>();
        int readOff = 0;
        for (Compiled.StaticRead each : Compiled.staticReads()) {
            Compiled.Site read = each.read();
            if (!read.owner().equals(BUDGET) || !settable.contains(read.member())
                    || read.from().equals(BUDGET)) {
                continue;
            }
            Compiled.Site taken = each.takenBy();
            if (taken != null && taken.owner().equals(BUDGET)
                    && READ_OFF.contains(taken.member())) {
                readOff++;
            } else {
                handedOn.add(read.at());
            }
        }
        assertTrue(readOff > 0, "some place reads a settable budget's figure, or nothing is read");
        Set<String> unsaid = new TreeSet<>(handedOn);
        unsaid.removeAll(NAMED_AS_A_BUDGET.keySet());
        assertEquals(List.of(), List.copyOf(unsaid),
                "these hand on a budget a compilation may set by itself, where a holder of the"
                        + " budget would tell the figure in force when it is read");
        Set<String> gone = new TreeSet<>(NAMED_AS_A_BUDGET.keySet());
        gone.removeAll(handedOn);
        assertEquals(List.of(), List.copyOf(gone), "these no longer name one");
    }
}
