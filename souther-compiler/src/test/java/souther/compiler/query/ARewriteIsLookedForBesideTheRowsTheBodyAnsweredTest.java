package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.ReplacementDisposition;

import java.util.Collection;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * A body answering one value is looked for a row beside the rows it answered, and not only among
 * the values its inputs' own rules offer.
 *
 * <p>A result that must hold an invariant leaves most of what the classes of an input offer without
 * an answer: the smallest values of a salary make an income below nothing, and the body does not
 * come back on them. The search then held nothing to compare the rewrite against and ended, though a
 * row the body answered on says where a run comes back, and one step from it the answer changes.
 */
class ARewriteIsLookedForBesideTheRowsTheBodyAnsweredTest {

    private static String hr(String incomeInvariant) {
        return """
                module example.hr

                data Yen = Int
                    invariant value >= 0
                data TotalIncome = Int
                    %s

                behavior deductionFor : (salary: Yen) -> Yen
                    constructs Yen

                let deductionFor (salary) =
                    if salary <= 1900000 then Yen(650000)
                    else if salary <= 3600000 then Yen(Rational.toInt(DOWN, salary.value * 30 / 100) + 80000)
                    else if salary <= 6600000 then Yen(Rational.toInt(DOWN, salary.value * 20 / 100) + 440000)
                    else Yen(1950000)

                behavior incomeFor : (salary: Yen) -> TotalIncome
                    constructs TotalIncome

                let incomeFor (salary) =
                    TotalIncome(salary.value - deductionFor(salary).value)

                example incomeFor
                    | "4.2 million of salary is 2.92 million of income" :
                        (Yen(4200000)) -> TotalIncome(2920000)
                """.formatted(incomeInvariant);
    }

    /**
     * Many whole numbers that change nothing, and one position the answer turns on. The row's list
     * is all the neighbours the first position offers, and none of them tells the rewrite apart;
     * the invariant of {@code Trigger} gives the classes values that do. A body with no fork is the
     * one a rewrite to a single answer is asked of.
     */
    private static final String NOISE = """
            module example.hr

            data Out = Int
            data Trigger = Int
                invariant value >= 0 && value <= 9

            behavior f : (noise: List<Int>, trigger: Trigger) -> Out
                constructs Out

            let f (noise, trigger) = Out(trigger.value)

            example f
                | "quiet" : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17], Trigger(5))
                    -> Out(5)
            """;

    private static ReplacementDisposition searched(String model, String behavior) {
        Compilation c = Compilation.ofSource(model, "Main");
        c.measure(Adequacy.Asked.fullReport());
        c.answerEverything();
        Collection<Replacements.Searched> all = c.db()
                .ask(new Replacements.Witnesses("example.hr", behavior)).value().values();
        assertEquals(1, all.size(), "the one answer the rows came to is the one rewrite");
        return all.iterator().next().disposition();
    }

    /** The values of the classes are refused at the result; the row's own neighbour is not. */
    @Test
    void aResultThatMustHoldAnInvariantIsToldByAValueBesideTheRow() {
        ReplacementDisposition came = searched(hr("invariant value >= 0"), "incomeFor");

        assertInstanceOf(ReplacementDisposition.Witnessed.class, came,
                () -> "one step from the salary that answered, the income is another: " + came);
    }

    /**
     * What the classes found, the neighbours do not take away.
     *
     * <p>Both searches spend the one run budget, so the one that goes first can leave nothing for
     * the other. The classes divide `trigger` at ten and find a row the rewrite answers differently
     * on; the neighbours of the row's list are a run of candidates that all answer alike.
     */
    @Test
    void whatTheClassesFoundIsNotLostToTheNeighboursSpendingTheRuns() {
        ReplacementDisposition came = searched(NOISE, "f");

        assertInstanceOf(ReplacementDisposition.Witnessed.class, came,
                () -> "the classes reach `trigger >= 10` and the neighbours of the list do not: "
                        + came);
    }

    /** The control: with nothing refusing the small values the classes still find a row. */
    @Test
    void whereNothingRefusesTheClassesStillFindOne() {
        assertInstanceOf(ReplacementDisposition.Witnessed.class, searched(hr(""), "incomeFor"));
    }
}
