package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.TestDay;
import souther.compiler.check.DateRules;
import souther.compiler.check.DeclaredSig;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.TypeCardinality;
import souther.compiler.meta.ModulePath;
import souther.compiler.numeric.Count;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;

import java.math.BigDecimal;
import java.time.LocalDate;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * What the declarations hold a date to is read whole only where every rule of it is one the
 * answer holds, and only where the date is a value of the question. A rule the answer does not
 * hold is said to be one, and a date under one case of a sum, asked of where a number under the
 * other case was fixed, is in no row: neither is ever answered as a date the rules leave open.
 */
class ADateIsReadWholeOnlyWhereEveryRuleOfItIsHeldTest {

    private static final String MODEL = """
            module g

            data A = { lo: Int }
            data B = { lo: Int, at: Date }
            data Q = A | B

            data Holder = { q: Q }

            data Ok

            behavior read : (h: Holder) -> Ok
            """;

    @Test
    void aDateUnderACaseNoRowIsInIsNotReadWhole() {
        InputDomain read = reading(MODEL);
        Quantities asked = read.quantities(rulesOf(MODEL));
        TermPath date = pathOf(read, "h.q@B.at");

        assertInstanceOf(DateRules.Whole.class, asked.rulesOfTheDateAt(date),
                "the date of a case nothing was fixed against is read whole");
        Quantities underA = asked.given(new NumericTerm.ValueOf(pathOf(read, "h.q@A.lo")),
                Count.of(BigDecimal.ONE));
        assertInstanceOf(DateRules.NotWhole.class, underA.rulesOfTheDateAt(date),
                "a date under the other case is no value of a row fixed under this one");
    }

    /**
     * Each rule of a date read for what it is: whole where the ends, the class of the parts and
     * the rules of two parts are all it says, and not whole where it says something they do not
     * hold — a choice, a part of the date moved, a hole in the date, or a moved part tied to
     * another field.
     */
    @Test
    void aDateIsReadWholeOnlyWhereEveryRuleOfItIsOneTheAnswerHolds() {
        Map<String, Class<? extends DateRules>> read = new LinkedHashMap<>();
        read.put("", DateRules.Whole.class);
        read.put("invariant Date.month(value) == 2", DateRules.Whole.class);
        read.put("invariant Date.day(value) - Date.month(value) >= 28", DateRules.Whole.class);
        read.put("invariant Date.day(value) == 1 || Date.day(value) == 15",
                DateRules.NotWhole.class);
        read.put("invariant Date.month(Date.addDays(1, value)) == 2", DateRules.NotWhole.class);
        read.put("invariant value /= Date(\"2020-01-01\")", DateRules.NotWhole.class);
        read.forEach((rule, expected) -> assertInstanceOf(expected, rulesOfTheDay(rule), rule));
    }

    /** The ends are the days the date's own rules leave it, and the rule of two parts is held
     *  with them. */
    @Test
    void theEndsAndTheRulesOfTwoPartsAreWhatTheRulesSay() {
        DateRules.Whole whole = assertInstanceOf(DateRules.Whole.class, rulesOfTheDay(
                "invariant value >= Date(\"2020-02-27\") && value <= Date(\"2020-03-02\")\n"
                        + "    invariant Date.day(value) - Date.month(value) >= 28"));
        assertEquals(LocalDate.of(2020, 2, 27).toEpochDay(), whole.least());
        assertEquals(LocalDate.of(2020, 3, 2).toEpochDay(), whole.most());
        assertEquals(1, whole.parts().size(), whole.parts()::toString);
    }

    /** A moved part tied to another field leaves the date what that field leaves it. */
    @Test
    void aMovedPartTiedToAnotherFieldIsNotReadWhole() {
        String model = """
                module g

                data Span = { start: Date, n: Int }
                    invariant early = Date.month(Date.addDays(1, start)) <= n

                data Ok

                behavior read : (s: Span) -> Ok
                """;
        InputDomain domain = reading(model);
        assertInstanceOf(DateRules.NotWhole.class, domain.quantities(rulesOf(model))
                .rulesOfTheDateAt(pathOf(domain, "s.start")));
    }

    /** What the declarations of {@code Day} hold its date to, under {@code rule}. */
    private static DateRules rulesOfTheDay(String rule) {
        String model = """
                module g

                data Day = Date
                    %s

                data Ok

                behavior read : (d: Day) -> Ok
                """.formatted(rule);
        InputDomain domain = reading(model);
        return domain.quantities(rulesOf(model)).rulesOfTheDateAt(pathOf(domain, "d"));
    }

    private static TermPath pathOf(InputDomain read, String spelled) {
        return read.positions().stream().map(Position::path)
                .filter(each -> each.toString().equals(spelled))
                .findFirst().orElseThrow(() -> new AssertionError(
                        "no position at " + spelled + " among " + read.positions().stream()
                                .map(Position::path).toList()));
    }

    private static Compilation compiled(String model) {
        return ACompiledModel.compiles(Compilation.ofSources(List.of(model), ModulePath.EMPTY));
    }

    private static RuleReadingSource rulesOf(String model) {
        Compilation compilation = compiled(model);
        return RuleReadings.of(compilation, compilation.modules().get(0));
    }

    private static InputDomain reading(String model) {
        Compilation compilation = compiled(model);
        String module = compilation.modules().get(0);
        Map<String, DeclaredSig> sigs =
                compilation.db().ask(new Bodies.DeclaredSignatures(module)).value();
        RuleReadingContext reading = RuleReadingContext.unshared(RuleReadings.of(compilation,
                module), ReadAs.THE_COMPILATION_DOES, TestDay.TODAY);
        return InputDomain.of(sigs.get("read"), reading,
                TypeCardinality.Counts.workedOutIn(reading),
                // Spelled out: this package declares a Membership of its own.
                souther.compiler.carrier.Membership.none());
    }
}
