package souther.bench;

import org.junit.jupiter.api.Test;

import souther.compiler.fmt.Deviations;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * That the shapes {@link Reporting} is timed against still depart from the canonical form, and
 * depart the way the measurement says they do.
 *
 * <p>{@link EveryShapeThatIsTimedStillCompilesTest} makes the same claim about the compile shapes,
 * and for the same reason: a source that stopped departing is a source the report answers about
 * faster, and nothing about a timing says that is what it timed. Here it is sharper. What the
 * measurement varies is the departure density, and a formatter change that makes one of these
 * sources canonical leaves two lines that differ in nothing being reported as the shape a product
 * shows up in and its control.
 *
 * <p>Three things, and each of them can go wrong on its own. That every declaration of the dense
 * shape departs — a shape whose departures thinned out measures the control twice. That exactly one
 * declaration of the control departs — a control that departed everywhere would be the dense shape
 * and the distance between the two lines would read as zero. And that the report is whole, because a
 * report that gives up before it reaches the canonical form does fewer rounds and is faster for it.
 *
 * <p>At small sizes. Whether a shape departs is not a question the size answers, and the sizes are
 * what the measurement varies.
 */
class EveryShapeThatIsTimedStillDepartsTest {

    /** Enough declarations that "every" and "one" are different numbers, and few enough that the
     *  report over them is not itself a benchmark. */
    private static final int DECLARATIONS = 8;

    /** A construct written down the page where the canonical form writes it on one line. */
    private static final String THE_WIDTH_BREAKS =
            "a construct whose line would exceed the width breaks";

    /** A level written at a column the canonical form does not write it at. */
    private static final String ONE_LEVEL_DEEPER = "one level deeper is one indent further in";

    @Test
    void everyDeclarationOfTheDenseGroupShapeDepartsFromItsGroup() {
        departsAt(DECLARATIONS, THE_WIDTH_BREAKS,
                Reporting.brokenGroups(DECLARATIONS, DECLARATIONS));
    }

    @Test
    void andOneDeclarationOfItsControlDoes() {
        departsAt(1, THE_WIDTH_BREAKS, Reporting.brokenGroups(DECLARATIONS, 1));
    }

    @Test
    void everyDeclarationOfTheDenseLevelShapeDepartsAtItsLevel() {
        departsAt(DECLARATIONS, ONE_LEVEL_DEEPER,
                Reporting.wrongIndents(DECLARATIONS, DECLARATIONS));
    }

    @Test
    void andOneDeclarationOfItsControlDoesToo() {
        departsAt(1, ONE_LEVEL_DEEPER, Reporting.wrongIndents(DECLARATIONS, 1));
    }

    /**
     * That the level shape departs at the column and at nothing else.
     *
     * <p>It is written down the page where the canonical form writes it down the page, so no group's
     * decision is departed from. A shape that also broke somewhere else would be timing both
     * projections under one name, and the two are what the measurement tells apart.
     */
    @Test
    void andTheLevelShapeDepartsAtNothingButItsColumns() {
        assertEquals(Set.of(ONE_LEVEL_DEEPER),
                rulesNamedBy(Reporting.wrongIndents(DECLARATIONS, DECLARATIONS)));
    }

    /** And the group shape departs at nothing but its groups. */
    @Test
    void andTheGroupShapeDepartsAtNothingButItsGroups() {
        assertEquals(Set.of(THE_WIDTH_BREAKS),
                rulesNamedBy(Reporting.brokenGroups(DECLARATIONS, DECLARATIONS)));
    }

    /**
     * That the two shapes differ in how many departed and in nothing else.
     *
     * <p>A dense shape and its control are read against each other, so what separates them has to be
     * the density. Held by writing the same declaration either way: what the control declares past
     * the first is what the dense shape declares, laid out as the canonical form lays it out.
     */
    @Test
    void andADensityIsTheDeparturesAndNothingElse() {
        for (List<String> pair : List.of(
                List.of(Reporting.brokenGroups(DECLARATIONS, DECLARATIONS),
                        Reporting.brokenGroups(DECLARATIONS, 1)),
                List.of(Reporting.wrongIndents(DECLARATIONS, DECLARATIONS),
                        Reporting.wrongIndents(DECLARATIONS, 1)))) {
            assertEquals(canonicalFormOf(pair.get(0)), canonicalFormOf(pair.get(1)),
                    "a shape and its control have different canonical forms, so a difference"
                            + " between their two lines is not about the departures");
        }
    }

    private static String canonicalFormOf(String source) {
        return souther.compiler.fmt.Formatter.format(source);
    }

    /**
     * That {@code source} departs at {@code expected} places, all of them named by {@code rule}, and
     * that the report saying so is whole.
     */
    private static void departsAt(int expected, String rule, String source) {
        Deviations.Report report = Deviations.of(source);
        assertTrue(report.whole(),
                "the report over this shape does not reach the canonical form, so it is timed"
                        + " giving up rather than answering");
        long named = report.deviations().stream().filter(d -> d.rule().equals(rule)).count();
        assertEquals(expected, named,
                "the shape departs at " + named + " place(s) under `" + rule + "` and the"
                        + " measurement reads it as " + expected);
    }

    /** Which rules a source's report names, in the order it names them. */
    private static Set<String> rulesNamedBy(String source) {
        Set<String> out = new LinkedHashSet<>();
        for (Deviations.Deviation d : Deviations.of(source).deviations()) {
            out.add(d.rule());
        }
        return out;
    }
}
