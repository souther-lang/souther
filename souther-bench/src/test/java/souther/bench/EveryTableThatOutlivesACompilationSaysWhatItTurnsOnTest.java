package souther.bench;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.Allowances;
import souther.compiler.partition.CompositionBudget;

import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A table held in a static field outlives every compilation, and what it holds is handed to each
 * compilation after the one that put it there. So what it holds must not turn on a figure a
 * compilation may hold to another ({@link Allowances#SETTABLE}) unless it is kept for that figure:
 * a count written out where the readings were wide and handed to a compilation held to narrow ones
 * is an answer to another question.
 *
 * <p>Asked of the fields themselves, because nothing in a table's own class says so. The figure a
 * result turns on is read by whatever computes it, a call or two away, and a table whose class
 * names no budget can still hold what turns on one; the one place left to say it is here, once for
 * each table. A table added arrives as a failure naming it, with the question to answer.
 *
 * <p>What this asks and what it does not. It asks that every table a compilation can put an answer
 * in is on the list with what it turns on: a map nothing can change is no table of answers, and a
 * map not made yet is one. It does not say that what is listed is true, which is read by whoever
 * lists it, nor that a value held in a map nothing can change was not made under a figure: a stop
 * made when the class is loaded and held in {@code Map.of} is asked by
 * {@code AFigureACompilationSetsIsReadWhereItIsUsedTest}, which follows what a class runs when it is
 * loaded. This is a list that makes a table's author say, and no proof of what they said.
 *
 * <p>Both ways round: a table in the list that no class holds any more is a rule about code that
 * has gone.
 */
class EveryTableThatOutlivesACompilationSaysWhatItTurnsOnTest {

    /** The maps nothing can change after they are made: the ones the library refuses to change, and
     *  the empty and single ones. Any other, a synchronized one included, can be. */
    private static boolean unchangeable(Object map) {
        return UNCHANGEABLE.contains(map.getClass());
    }

    /** What the library makes of a map it will not change, read off a value of each kind. */
    private static final Set<Class<?>> UNCHANGEABLE = new HashSet<>(List.of(
            Map.of().getClass(), Map.of(1, 1).getClass(), Map.of(1, 1, 2, 2).getClass(),
            Collections.unmodifiableMap(new HashMap<>()).getClass(),
            Collections.unmodifiableSequencedMap(new LinkedHashMap<>()).getClass(),
            Collections.unmodifiableSortedMap(new TreeMap<>()).getClass(),
            Collections.emptyMap().getClass(), Collections.singletonMap(1, 1).getClass()));

    private static final String FOR_THE_FIGURE = "turns on the readings of one condition and is kept"
            + " for the figure in force";

    private static final String OF_ITS_KEY = "holds what is worked out of its key alone, which no"
            + " budget of this compiler's turns on";

    private static final String READ_ONLY = "is filled once when the class is loaded, out of what is"
            + " written in the compiler, and read after: no answer of a compilation's is put in it";

    private static final String EMPTY_OF_THE_COMPILERS_OWN = "is the empty value of a map of this"
            + " compiler's own, which has no way to put anything in it";

    private static final String SHARES = "keeps one of each value that is equal, which says nothing"
            + " that turns on a figure";

    /** Each table, by the class and field that hold it, and what it turns on. */
    private static final Map<String, String> TURNS_ON = Map.ofEntries(
            Map.entry("souther.compiler.meaning.CountsWrittenOut#HANDED", FOR_THE_FIGURE),
            Map.entry("souther.compiler.meaning.CountsWrittenOut#HANDED_OUTSIDE_ELEMENTS",
                    FOR_THE_FIGURE),
            Map.entry("souther.compiler.meaning.SharedPropositions#CHOICES", FOR_THE_FIGURE),
            Map.entry("souther.compiler.meaning.SharedPropositions#WRITTEN",
                    "turns on budgets none of which a compilation may set, named in"
                            + " WHILE_NOT_SET and refused where one is"),
            Map.entry("souther.compiler.meaning.SharedPropositions#KEPT", SHARES),
            Map.entry("souther.compiler.partition.OnTheWay$OneOf#MADE", SHARES),
            Map.entry("souther.compiler.inputs.TermPath#FILED", SHARES),
            Map.entry("souther.compiler.inputs.RepresentationBounds#UP_TO", OF_ITS_KEY),
            Map.entry("souther.compiler.partition.CaseMaps#MADE", OF_ITS_KEY),
            Map.entry("souther.compiler.partition.MonthsAndDaysOfOneDate#EVERY_YEAR", OF_ITS_KEY),
            Map.entry("souther.compiler.partition.DatesThatStandInEveryYear#KNOWN", OF_ITS_KEY),
            Map.entry("souther.compiler.partition.YearsAWayAllows#CLASSES", OF_ITS_KEY),
            Map.entry("souther.compiler.coverage.DecisionSources$LibraryPart#KEPT", OF_ITS_KEY),
            Map.entry("souther.compiler.regex.EndsOfAMachine#HELD", OF_ITS_KEY),
            Map.entry("souther.compiler.regex.Recognizer#BUILT", OF_ITS_KEY),
            Map.entry("souther.compiler.regex.StringsHeldAsWritten#MADE", OF_ITS_KEY),
            Map.entry("souther.compiler.check.BindingMap#EMPTY", EMPTY_OF_THE_COMPILERS_OWN),
            Map.entry("souther.compiler.collect.InTheOrderGiven#NO_ENTRIES",
                    EMPTY_OF_THE_COMPILERS_OWN),
            Map.entry("souther.compiler.fmt.Spacing#DECIDED", READ_ONLY),
            Map.entry("souther.compiler.fmt.Spacing#FACES", READ_ONLY),
            Map.entry("souther.compiler.check.WhatALibraryLeavesAsShipped$Shipped#READS",
                    READ_ONLY),
            Map.entry("souther.compiler.partition.ReadingState#FIELDS",
                    "the fields of a class, which is no answer of a compilation's"),
            Map.entry("souther.compiler.revision.RevisionWorkDone#DONE",
                    "a count of the work done, which no answer is worked out of"));

    /**
     * The budgets a table turns on where it is kept for no figure, which are safe only while no
     * compilation may hold them to another: the cases written out of a statement over the ways turn
     * on how many parts a step concludes with and how many ways a statement is written out over.
     */
    private static final Map<String, Set<CompositionBudget>> WHILE_NOT_SET = Map.of(
            "souther.compiler.meaning.SharedPropositions#WRITTEN",
            Set.of(CompositionBudget.PARTS_A_DERIVATION_CONCLUDES,
                    CompositionBudget.WAYS_A_STATEMENT_IS_WRITTEN_OUT_OVER));

    /** What a table is listed as turning on only while a budget is not set is no longer so once it
     *  is: it is then kept for every compilation, and turns on the figure of one. */
    @Test
    void noTableListedAsTurningOnABudgetIsOneACompilationMayNowSet() {
        assertTrue(TURNS_ON.keySet().containsAll(WHILE_NOT_SET.keySet()),
                "a table is said to turn on a budget, and is not listed");
        Map<String, Set<CompositionBudget>> nowSettable = new TreeMap<>();
        WHILE_NOT_SET.forEach((table, budgets) -> {
            Set<CompositionBudget> met = new TreeSet<>(budgets);
            met.retainAll(Allowances.SETTABLE);
            if (!met.isEmpty() || budgets.isEmpty()) {
                nowSettable.put(table, met);
            }
        });
        assertEquals(Map.of(), nowSettable,
                "these turn on a budget a compilation may set now, or on none, and are kept for"
                        + " the figure of whichever compilation filled them: key them by it, as"
                        + " CountsWrittenOut is, and list them for the figure");
    }

    @Test
    void everyTableAStaticFieldHoldsSaysWhatItTurnsOn() throws Exception {
        assertFalse(Allowances.SETTABLE.isEmpty(), "some figure may be set, or nothing turns on one");
        Set<String> classes = new TreeSet<>();
        for (Compiled.Site site : Compiled.sites()) {
            if (site.from().startsWith("souther.compiler.")) {
                classes.add(site.from());
            }
        }
        Set<String> found = new TreeSet<>();
        for (String name : classes) {
            Class<?> held;
            try {
                held = Class.forName(name, false, getClass().getClassLoader());
            } catch (ClassNotFoundException | LinkageError e) {
                continue;
            }
            for (Field each : held.getDeclaredFields()) {
                if (Modifier.isStatic(each.getModifiers())
                        && Map.class.isAssignableFrom(each.getType())) {
                    each.setAccessible(true);
                    Object value = each.get(null);
                    // A map not made yet is one made when it is first used, which is to say a
                    // table: nothing else is left null in a field of that type.
                    if (value == null || !unchangeable(value)) {
                        found.add(name + "#" + each.getName());
                    }
                }
            }
        }
        assertFalse(found.isEmpty(), "some class holds a table, or this reads no field");

        Set<String> unsaid = new TreeSet<>(found);
        unsaid.removeAll(TURNS_ON.keySet());
        assertEquals(List.of(), List.copyOf(unsaid),
                "these hold a table that outlives every compilation, and nothing says what it turns"
                        + " on: if it holds what turns on a figure a compilation may set, it is kept"
                        + " for that figure, as CountsWrittenOut is");
        Set<String> gone = new TreeSet<>(TURNS_ON.keySet());
        gone.removeAll(found);
        assertEquals(List.of(), List.copyOf(gone), "these hold no such table any more");
    }
}
