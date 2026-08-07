package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.query.Compilation;
import souther.compiler.query.Shapes;
import souther.compiler.types.TypeName;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a field can hold where the record it sits in has a rule about it.
 *
 * <p>A field's type says what values exist of that type. It does not say which of them this record
 * will accept in this position, and a rule relating two fields is exactly the difference. Reading the
 * type alone is what issue #427 reports: a day's minutes run to 1440, so both ends of an interval are
 * offered 1440, and one of them is a value no interval can be built with.
 */
class AFieldsRangeIsTheRecordsRuleProjectedOntoItTest {

    private static FieldDomains domainsIn(String source, String type) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Symbols symbols = compilation.db().ask(new Shapes.Scope(module)).value();
        assertNotNull(symbols, "the model did not compile");
        TypeName named = new TypeName(module, type);
        Ast.Data data = (Ast.Data) symbols.get(named);
        assertNotNull(data, "no `" + type + "` in " + module);
        return FieldDomains.of(named, data, symbols);
    }

    private static void assertBounds(NumericDomain.Bounds bounds, long min, long max) {
        assertNotNull(bounds, "nothing bounds this field");
        assertEquals(0, BigDecimal.valueOf(min).compareTo(bounds.min()), "min was " + bounds.min());
        assertEquals(0, BigDecimal.valueOf(max).compareTo(bounds.max()), "max was " + bounds.max());
    }

    private static final String TIMESHEET = """
            module example.timesheet

            data MinuteOfDay = Int
                invariant withinDay = value >= 0 && value <= 1440

            data WorkInterval =
                { startsAt: MinuteOfDay
                , endsAt: MinuteOfDay
                }
                invariant endsAfterStart = startsAt < endsAt
            """;

    @Test
    void aSiblingsRuleNarrowsBothEndsOfTheRange() {
        FieldDomains domains = domainsIn(TIMESHEET, "WorkInterval");

        assertBounds(domains.at("startsAt"), 0, 1439);
        assertBounds(domains.at("endsAt"), 1, 1440);
        assertTrue(domains.exact(), "both rules were read, so these are the whole of what is allowed");
    }

    /** Without the sibling rule the field's own type is the whole answer, so nothing moves. Held so
     * that the narrowing above is read as the rule doing it and not as an off-by-one. */
    @Test
    void withoutTheRuleTheTypesOwnBoundIsTheRange() {
        FieldDomains domains = domainsIn("""
                module example.timesheet

                data MinuteOfDay = Int
                    invariant withinDay = value >= 0 && value <= 1440

                data WorkInterval =
                    { startsAt: MinuteOfDay
                    , endsAt: MinuteOfDay
                    }
                """, "WorkInterval");

        assertBounds(domains.at("startsAt"), 0, 1440);
        assertBounds(domains.at("endsAt"), 0, 1440);
    }

    /** A non-strict rule between two fields of one type narrows neither. Every relational record
     * invariant in souther-examples is this shape, which is why none of them moves a boundary. */
    @Test
    void aNonStrictRuleBetweenFieldsOfOneTypeNarrowsNothing() {
        FieldDomains domains = domainsIn("""
                module example.shift

                data Hours = Int
                    invariant withinDay = value >= 0 && value <= 24

                data DailyAttendance =
                    { worked: Hours
                    , lateNight: Hours
                    }
                    invariant lateNightIsPartOfIt = lateNight <= worked
                """, "DailyAttendance");

        assertBounds(domains.at("worked"), 0, 24);
        assertBounds(domains.at("lateNight"), 0, 24);
    }

    /** Over decimals there is no next value, so a strict rule takes nothing off either end. */
    @Test
    void aStrictRuleOverDecimalsNarrowsNothing() {
        FieldDomains domains = domainsIn("""
                module example.band

                data Ratio = Decimal
                    invariant withinOne = value >= 0.0m && value <= 1.0m

                data Band =
                    { low: Ratio
                    , high: Ratio
                    }
                    invariant ordered = low < high
                """, "Band");

        assertBounds(domains.at("low"), 0, 1);
        assertBounds(domains.at("high"), 0, 1);
    }

    /** A length is a whole number like any other, so a rule relating one to a field is in the
     * fragment and narrows through it: a label of at least one character puts {@code startsAt} at 2
     * or more. */
    @Test
    void aRuleAgainstALengthNarrowsThroughTheLengthsOwnBound() {
        FieldDomains domains = domainsIn("""
                module example.timesheet

                data MinuteOfDay = Int
                    invariant withinDay = value >= 0 && value <= 1440

                data Label = String
                    invariant named = String.length(value) >= 1

                data WorkInterval =
                    { startsAt: MinuteOfDay
                    , endsAt: MinuteOfDay
                    , label: Label
                    }
                    invariant endsAfterStart = startsAt < endsAt
                    invariant afterTheLabel = String.length(label.value) < startsAt.value
                """, "WorkInterval");

        assertBounds(domains.at("startsAt"), 2, 1439);
        assertTrue(domains.exact(), "both rules are comparisons of whole numbers");
    }

    /** A rule that is not a comparison holds no bound to derive through. It narrows nothing, it is
     * still a way the record refuses a value, and so the bounds stop being all of what the
     * declaration says. */
    @Test
    void aRuleThatIsNotAComparisonLeavesTheAnswerInexact() {
        FieldDomains domains = domainsIn("""
                module example.timesheet

                data MinuteOfDay = Int
                    invariant withinDay = value >= 0 && value <= 1440

                data Label = String

                data WorkInterval =
                    { startsAt: MinuteOfDay
                    , endsAt: MinuteOfDay
                    , label: Label
                    }
                    invariant endsAfterStart = startsAt < endsAt
                    invariant spelled = String.matches("[a-z]+", label.value)
                """, "WorkInterval");

        assertBounds(domains.at("startsAt"), 0, 1439);
        assertFalse(domains.exact(),
                "nothing here says a label matching that pattern exists, so 1439 is not promised");
    }

    /** A field nothing says anything about has no bounds rather than empty ones. */
    @Test
    void aFieldWithNoRuleAtAllIsAbsent() {
        FieldDomains domains = domainsIn("""
                module example.plain

                data Note = String

                data Entry =
                    { count: Int
                    , note: Note
                    }
                """, "Entry");

        assertNull(domains.at("note"), "a string has no numbers to bound");
        assertNull(domains.at("count"), "an Int the model draws no line through is unbounded");
    }

    /** A newtype has no siblings, so there is nothing here to project. */
    @Test
    void aNewtypeHasNothingToProjectOnto() {
        assertEquals(FieldDomains.NONE.exact(), domainsIn(TIMESHEET, "MinuteOfDay").exact());
        assertNull(domainsIn(TIMESHEET, "MinuteOfDay").at("value"));
    }
}
