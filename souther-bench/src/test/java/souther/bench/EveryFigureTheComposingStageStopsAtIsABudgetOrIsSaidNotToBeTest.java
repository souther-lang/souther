package souther.bench;

import org.junit.jupiter.api.Test;

import java.lang.classfile.ClassModel;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Every whole number the composing stage is written to stop at is one of this compiler's budgets, or
 * is said here not to be.
 *
 * <p>The second sheet, beside the one that counts where a budget is read. That one holds the
 * registered figures to being carried; this one holds the classes to registering a figure at all —
 * and it is the sheet the population needed. Twice while #1232 was written the budgets were taken
 * from the constants that looked like budgets, and twice the list was short. A name is not what
 * makes a budget.
 *
 * <p><b>Told by how the number arrives and not by what it is called.</b> A figure that comes from
 * {@link souther.compiler.partition.CompositionBudget} is worked out when the class is initialised
 * and has no constant value in the class file; a number written into the source has one. So a
 * constant that is a budget is one nobody wrote down twice, and this is what says so mechanically —
 * a rule about spelling would be passed by the next figure spelled differently, which is the failure
 * that made this necessary.
 *
 * <p>What it still does not see is a figure derived from something other than a number, which is
 * anything worked out rather than written down. Every figure there is is written down as one of
 * this compiler's budgets, so what such a number would be is a bound somebody put beside a walk
 * without registering it — and that one is caught by the other sheet, which sees the enum being
 * read where the walk stops. Neither is enough alone.
 */
class EveryFigureTheComposingStageStopsAtIsABudgetOrIsSaidNotToBeTest {

    /** Where a row for a coverage item is composed, which is what a budget of this kind bounds. */
    private static final String COMPOSING = "souther.compiler.partition.";

    /**
     * The whole numbers written into these classes, and why each is not a figure a search stops at.
     *
     * <p>One entry per constant, with what it is instead. A number added is a question — is this
     * something this compiler stops at, and does what stops there carry it — and the answer belongs
     * beside the code that stops.
     */
    private static final Map<String, String> NOT_A_BUDGET = new LinkedHashMap<>(Map.ofEntries(
            // How far a part of a date runs, which is the calendar's and not this compiler's. A
            // walk over every one of them is what makes an answer of nothing a statement about
            // dates, so raising either would be writing down a month no year has.
            Map.entry("souther.compiler.partition.TermRealizations.MONTHS_A_YEAR_HAS",
                    "how many months a year has, which is what a month may stand at"),
            Map.entry("souther.compiler.partition.TermRealizations.DAYS_THE_LONGEST_MONTH_HAS",
                    "how far the days run in the longest month, which is as far as a day runs"),

            // The calendar's cycle and the stretch of years a proof about it is made over: what has
            // to be looked at for an answer to hold of every year, not how far a search goes.
            Map.entry("souther.compiler.partition.DatesThatStandInEveryYear.FIRST_YEAR",
                    "where the four hundred years that stand for every year start"),
            Map.entry("souther.compiler.partition.DatesThatStandInEveryYear.YEARS_OF_A_CYCLE",
                    "how many years the calendar's pattern repeats over"),
            Map.entry("souther.compiler.partition.YearsAWayAllows.YEARS_OF_A_CYCLE",
                    "how many years the calendar's pattern repeats over, which is as many years"
                            + " as a look from one year meets every pattern in"),
            // A way that states the parts or the years of more dates than this is not asked, and
            // nothing is then claimed of the years or the months and days it names; no search
            // stops at it.
            Map.entry("souther.compiler.partition.YearsAWayAllows.MOST_DATES",
                    "how many dates a way may state the years of for them to be chosen together"),
            Map.entry("souther.compiler.partition.WhatStatementsOfDatePartsLeaveAlone"
                            + ".MOST_DATES_A_WAY_IS_ASKED_OF",
                    "how many dates a way may state the parts of for them to be looked through"),

            // A distance no assignment reaches, which a position with no class to move to is at.
            Map.entry("souther.compiler.partition.NearestAssignments.UNREACHABLE",
                    "no distance, which is what a position with no class to move to changes"
                            + " a distance by"),

            // A place in a list rather than an amount of anything.
            Map.entry("souther.compiler.partition.Generator.NOT_HERE",
                    "no position, which is what an index that found none is"),

            // How much of a number is written down, which bounds a value's shape and not a search:
            // any length is sound while the rounding goes outward, so nothing is left unlooked at.
            Map.entry("souther.compiler.partition.LevelRealizer.DIGITS_A_DERIVED_END_KEEPS",
                    "how far a derived end is written out, which leaves nothing untried"),

            // Budgets of walks that are not the composing of a row at a coverage item. Each bounds
            // a search of its own, and what reaching one costs is that search's to carry — measured
            // for #1232 and left where they are, which is why they are named rather than omitted.
            Map.entry("souther.compiler.partition.Generator.MOST_REPAIRS",
                    "the walk over which classes to settle a row at, not the row at an item"),
            Map.entry("souther.compiler.partition.Generator.MOST_LOOKS",
                    "how many assignments one search for a row looks at, passed over or built"),
            Map.entry("souther.compiler.partition.Generator.MOST_INTERPRETATIONS",
                    "how many readings of a row's values one run tries"),
            Map.entry("souther.compiler.partition.Generator.MOST_RUNS_PER_INTERPRETATION",
                    "how many runs one reading of a row's values is given"),
            Map.entry("souther.compiler.partition.StandingAtAPoint.MOST_READINGS",
                    "how many element-wise readings of one row a point is tried against"),

            // Which candidates a row for a case of a statement is built from. The search for such
            // a row says the rows it found and nothing of the cases it did not: a case with no row
            // is not found, which is not out of reach, so there is no figure it came back with.
            Map.entry("souther.compiler.partition.CaseCandidates.MOST_LEVELS_BELOW_THE_START",
                    "how many levels below the start of a search a node meeting it is looked for"
                            + " at, which bounds the candidates and claims nothing of the model"),
            Map.entry("souther.compiler.partition.KeyOrderCandidates.MOST_VALUES_OF_A_KIND",
                    "how many distinct values of one kind the two copies of an element are given"
                            + " between them; a case with no row is not found, which claims"
                            + " nothing of the model"),
            Map.entry("souther.compiler.partition.KeyOrderCandidates.MOST_LEVELS_OF_FIELDS",
                    "how many records down an element a field is looked for to be given another"
                            + " value where the statement does not name one; a field past it is"
                            + " not varied, which claims nothing of the model"),
            Map.entry("souther.compiler.partition.KeyOrderCandidates.MOST_REWRITES_LOOKED_AT",
                    "how many rewrites of one row are looked at for the order of a repeated key,"
                            + " admitted by the decoder or not; a case with no row is not found,"
                            + " which claims nothing of the model"),
            Map.entry("souther.compiler.partition.KeyOrderCandidates.MOST_CANDIDATES",
                    "how many rewrites of one row are run for the order of a repeated key; a case"
                            + " with no row is not found, which claims nothing of the model"),

            // What counts are composed against the total of their container, and past which they
            // are composed as any are. No search runs to them and stops there: they say which
            // statements this takes, and a statement past them is not stopped but left to the
            // composing that does not read the total.
            Map.entry("souther.compiler.partition.CoupledCardinalityComposer.MOST_STATEMENTS",
                    "how many counts are composed together against a total; past it the counts"
                            + " are composed one at a time as they are elsewhere"),
            Map.entry("souther.compiler.partition.CoupledCardinalityComposer.MOST_RELATIONS",
                    "how many relations of those counts have their ways of standing taken"
                            + " together; past it the counts are composed as elsewhere"),

            // A choice among rows that all stand at the item, which ends with one taken whatever
            // it comes to, so nothing is left owed for reaching it.
            Map.entry("souther.compiler.partition.Generator.MOST_ROWS_OFFERED_FOR_THE_ARMS",
                    "how many rows meeting one requirement are looked through for one its arms"
                            + " answer differently on; reaching it stops no search, since a row"
                            + " is taken either way")));

    /**
     * A number written into a composing class is a budget's, or is one of the above.
     *
     * <p>Both ways round, as the other sheet is. A number nobody has said anything about is one
     * somebody has to decide about; an entry naming a constant that has gone is a rule about code
     * that is not there.
     */
    @Test
    void aFigureIsThisCompilersBudgetOrIsSaidToBeSomethingElse() {
        List<String> written = new ArrayList<>();
        for (ClassModel model : Reactor.classes()) {
            String from = model.thisClass().asInternalName().replace('/', '.').replace('$', '.');
            if (!from.startsWith(COMPOSING) || from.equals(COMPOSING + "CompositionBudget")) {
                continue;
            }
            for (var field : model.fields()) {
                if (!field.fieldTypeSymbol().descriptorString().equals("I")
                        || field.findAttribute(java.lang.classfile.Attributes.constantValue())
                                .isEmpty()) {
                    continue;   // not a whole number, or worked out rather than written down
                }
                written.add(from + "." + field.fieldName().stringValue());
            }
        }

        List<String> unsaid = new ArrayList<>(written);
        unsaid.removeAll(NOT_A_BUDGET.keySet());
        List<String> gone = new ArrayList<>(NOT_A_BUDGET.keySet());
        gone.removeAll(written);

        assertEquals(List.of(), NOT_A_BUDGET.isEmpty() || written.isEmpty()
                        ? List.of("nothing was read, so this asserts nothing") : List.of(),
                "the classes were read and hold whole numbers, or the census found none and"
                        + " everything below passes by looking at nothing");
        assertEquals(List.of(), unsaid,
                "a whole number written into a composing class that nothing says anything about."
                        + " Either a search stops at it — and then it is a CompositionBudget, whose"
                        + " figure the class reads rather than writing its own — or it is something"
                        + " else and the list above says what");
        assertEquals(List.of(), gone, "a rule about a constant that is no longer written");
    }
}
