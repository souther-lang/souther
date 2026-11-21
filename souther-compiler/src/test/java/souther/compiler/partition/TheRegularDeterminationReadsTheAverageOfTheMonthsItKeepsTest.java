package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.test.Nightly;
import souther.compiler.ACompiledModel;
import souther.compiler.NotRead;
import souther.compiler.StopsTheReportSays;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * The regular determination of a health-insurance grade, as a model of social insurance writes
 * it: the average of the remuneration of the months a filter keeps of three, each amount the sum
 * of five held one place at a time, looked up in a table of fifty ascending lower bounds.
 *
 * <p>The declarations are the ones the decision is read through, written as that model writes
 * them, and nothing else of it. The total is over no more months than the three the filter keeps
 * from, each at most five times the bound on one amount, so it lies within an {@code Int}, and the
 * lookup's comparison is read; with the amounts unbounded the total can pass the type, and the
 * run that gets there is said to stop. What else the model leaves open — whether the month the
 * decision applies from is built — is the date's to say, and is no line about the total.
 *
 * <p>Deferred to the night for what it costs: the fifty rows of the table the lookup walks, read
 * twice. The same reading of a total over what a filter keeps is asked on every change of models
 * without the table ({@link ATotalOfWhatAFilterKeepsIsHeldToTheListItKeepsFromTest},
 * {@link AnAverageOfAmountsBoundedOnePlaceEachIsReadWhereItIsLookedUpTest}); what this adds is the
 * model as it is written, which is as well found by the morning as by the change.
 */
@Nightly
class TheRegularDeterminationReadsTheAverageOfTheMonthsItKeepsTest {

    private static final String MODEL = """
            module hr

            data Yen = Int
                invariant value >= 0

            data MonthlyRemuneration =
                { baseSalary: Yen
                , scheduledAllowances: Yen
                , commutingAllowance: Yen
                , excludedAllowances: Yen
                , variableAllowances: Yen
                }
            BOUNDS

            let scheduledWage (r: MonthlyRemuneration): Yen = r.baseSalary + r.scheduledAllowances
            let fixedRemuneration (r: MonthlyRemuneration): Yen =
                scheduledWage(r) + r.commutingAllowance + r.excludedAllowances
            let totalRemuneration (r: MonthlyRemuneration): Yen = fixedRemuneration(r) + r.variableAllowances

            data HealthGrade = Int
                invariant value >= 1 && value <= 50
            data PensionGrade = Int
                invariant value >= 1 && value <= 32

            data ContributionMonth = Date
                invariant Date.day(value) == 1

            data GradeRow =
                { grade: HealthGrade
                , standard: Yen
                , lowerBound: Yen
                }

            let ascendingStep (carried: (Int, Bool), r: GradeRow): (Int, Bool) = {
                let (previous, ascending) = carried
                (r.lowerBound.value, ascending && previous <= r.lowerBound.value)
            }

            let ascendingFrom (rows: List<GradeRow>): Bool = {
                let (last, ascending) = List.fold((carried, r) -> ascendingStep(carried, r), (0, true), rows)
                ascending
            }

            data GradeTable = List<GradeRow>
                invariant fiftyRows = List.length(value) == 50
                invariant distinctGrades = List.allDistinctBy(.grade, value)
                invariant ascendingBounds = ascendingFrom(value)

            let gradeRow (g: Int, standard: Int, lowerBound: Int): GradeRow =
                GradeRow { grade = HealthGrade(g), standard = Yen(standard), lowerBound = Yen(lowerBound) }

            let standardGradeTable = GradeTable(
                [ gradeRow(1,    58000,       0), gradeRow(2,    68000,   63000)
                , gradeRow(3,    78000,   73000), gradeRow(4,    88000,   83000)
                , gradeRow(5,    98000,   93000), gradeRow(6,   104000,  101000)
                , gradeRow(7,   110000,  107000), gradeRow(8,   118000,  114000)
                , gradeRow(9,   126000,  122000), gradeRow(10,  134000,  130000)
                , gradeRow(11,  142000,  138000), gradeRow(12,  150000,  146000)
                , gradeRow(13,  160000,  155000), gradeRow(14,  170000,  165000)
                , gradeRow(15,  180000,  175000), gradeRow(16,  190000,  185000)
                , gradeRow(17,  200000,  195000), gradeRow(18,  220000,  210000)
                , gradeRow(19,  240000,  230000), gradeRow(20,  260000,  250000)
                , gradeRow(21,  280000,  270000), gradeRow(22,  300000,  290000)
                , gradeRow(23,  320000,  310000), gradeRow(24,  340000,  330000)
                , gradeRow(25,  360000,  350000), gradeRow(26,  380000,  370000)
                , gradeRow(27,  410000,  395000), gradeRow(28,  440000,  425000)
                , gradeRow(29,  470000,  455000), gradeRow(30,  500000,  485000)
                , gradeRow(31,  530000,  515000), gradeRow(32,  560000,  545000)
                , gradeRow(33,  590000,  575000), gradeRow(34,  620000,  605000)
                , gradeRow(35,  650000,  635000), gradeRow(36,  680000,  665000)
                , gradeRow(37,  710000,  695000), gradeRow(38,  750000,  730000)
                , gradeRow(39,  790000,  770000), gradeRow(40,  830000,  810000)
                , gradeRow(41,  880000,  855000), gradeRow(42,  930000,  905000)
                , gradeRow(43,  980000,  955000), gradeRow(44, 1030000, 1005000)
                , gradeRow(45, 1090000, 1055000), gradeRow(46, 1150000, 1115000)
                , gradeRow(47, 1210000, 1175000), gradeRow(48, 1270000, 1235000)
                , gradeRow(49, 1330000, 1295000), gradeRow(50, 1390000, 1355000)
                ])

            let gradeRowFor (monthly: Yen): GradeRow =
                List.fold((acc, r) -> if r.lowerBound <= monthly then r else acc,
                          gradeRow(1, 58000, 0),
                          standardGradeTable.value)

            let pensionGradeOf (health: HealthGrade): PensionGrade =
                PensionGrade(Int.clamp(1, 32, health.value - 3))

            data DeterminationBasis = OnAcquisition | RegularDetermination | OccasionalRevision

            data GradeDecision =
                { basis: DeterminationBasis
                , standard: Yen
                , health: HealthGrade
                , pension: PensionGrade
                , appliesFrom: ContributionMonth
                }

            let decisionFor (basis: DeterminationBasis, monthly: Yen, appliesFrom: ContributionMonth): GradeDecision = {
                let row = gradeRowFor(monthly)
                GradeDecision { basis = basis
                              , standard = row.standard
                              , health = row.grade
                              , pension = pensionGradeOf(row.grade)
                              , appliesFrom = appliesFrom
                              }
            }

            data PaidBaseDays = Int
                invariant value >= 0 && value <= 31

            data MonthlyPayRecord =
                { month: ContributionMonth
                , paidBaseDays: PaidBaseDays
                , remuneration: MonthlyRemuneration
                }

            data ThreeMonthWindow =
                { first: MonthlyPayRecord
                , second: MonthlyPayRecord
                , third: MonthlyPayRecord
                }

            let monthsOf (w: ThreeMonthWindow): List<MonthlyPayRecord> = [ w.first, w.second, w.third ]

            let payableMonths (w: ThreeMonthWindow): List<MonthlyPayRecord> =
                List.filter(r -> r.paidBaseDays >= 17, monthsOf(w))

            let averageRemuneration (records: List<MonthlyPayRecord>): Yen =
                Yen(Rational.toInt(DOWN,
                    List.sum(List.map(r -> totalRemuneration(r.remuneration).value, records))
                    / List.length(records)))

            data NoPayableMonth

            behavior decideRegularly : (window: ThreeMonthWindow) -> GradeDecision | NoPayableMonth
                constructs GradeDecision, GradeRow, GradeTable, HealthGrade, PensionGrade, ContributionMonth,
                           Yen

            let decideRegularly (window) = {
                let payable = payableMonths(window)
                guard List.length(payable) >= 1 else NoPayableMonth
                let september = ContributionMonth(Date.addMonths(9 - Date.month(window.first.month.value), window.first.month.value))
                decisionFor(RegularDetermination, averageRemuneration(payable), september)
            }
            """;

    private static final String BOUNDED = """
                invariant baseSalary.value <= 1000000000000
                invariant scheduledAllowances.value <= 1000000000000
                invariant commutingAllowance.value <= 1000000000000
                invariant excludedAllowances.value <= 1000000000000
                invariant variableAllowances.value <= 1000000000000""";

    /** The model, the amounts held by {@code bounds}, measured. */
    private static Compilation measured(String bounds) {
        Compilation compilation = Compilation.ofSource(MODEL.replace("BOUNDS", bounds), "Main");
        // The readings of the lookup and of the total, and no row looked for, which nothing here
        // asks about.
        compilation.measure(new Adequacy.Asked(Adequacy.Level.OFF, false));
        ACompiledModel.compiles(compilation);
        return compilation;
    }

    /** The operations over the months' remuneration a stop is said of, as written. */
    private static List<String> stopsInTheTotal(Compilation compilation) {
        return StopsTheReportSays.of(compilation).stops().stream()
                .flatMap(stop -> stop.operations().stream())
                .map(StopsTheReportSays.Operation::written)
                .filter(written -> written != null && written.contains("remuneration"))
                .toList();
    }

    /** No comparison is left unread, and nothing is said to stop in the total; the control,
     *  with each amount unbounded above, is said to. */
    @Test
    void theLookupOfTheAverageIsRead() {
        Compilation bounded = measured(BOUNDED);
        assertEquals(List.of(), AdequacyReport.of(bounded)
                .humanInEnglish(SourceRendering.namedByIdentity(bounded.texts())).lines()
                .filter(NotRead::isOne).toList());
        assertEquals(List.of(), stopsInTheTotal(bounded));
        assertFalse(stopsInTheTotal(measured("")).isEmpty(), "control");
    }
}
