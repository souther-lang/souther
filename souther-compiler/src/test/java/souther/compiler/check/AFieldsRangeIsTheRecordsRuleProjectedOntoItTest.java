package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.query.Compilation;
import souther.compiler.query.Shapes;
import souther.compiler.types.TypeName;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.util.List;

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
        assertTrue(domains.exact("startsAt"), "both rules were read");
        assertTrue(domains.exact("endsAt"));
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
        assertFalse(domains.exact("low"),
                "the true range is open at one end, which these bounds cannot hold, so 1 is not"
                        + " promised to be writable");
        assertFalse(domains.exact("high"));
    }

    /** A rule that skips a value is a hole in a range, and a range is all the domain holds. The bound
     * stays where the type left it and says it is not the whole story. */
    @Test
    void aRuleThatSkipsAValueLeavesTheAnswerInexact() {
        FieldDomains domains = domainsIn("""
                module example.skip

                data N = Int
                    invariant within = value >= 0 && value <= 10

                data R =
                    { a: N
                    }
                    invariant nonzero = a.value /= 0
                """, "R");

        assertBounds(domains.at("a"), 0, 10);
        assertFalse(domains.exact("a"), "0 is in these bounds and no row can write it");
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
        assertTrue(domains.exact("startsAt"), "both rules are comparisons of whole numbers");
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
        assertTrue(domains.exact("startsAt"),
                "the pattern is a rule about the label and says nothing about the minutes");
        assertFalse(domains.exact("label"), "and it is the whole of what is known about the label");
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

    /**
     * A newtype over a newtype is bounded by neither reading.
     *
     * <p>The range a boundary is derived from and the range this projects are read by two different
     * walks, and what matters is that they agree: a bound only one of them found would narrow one end
     * of a position and leave the other where its type left it, which is not a range of anything.
     * They agree here on nothing — `data StartMinute = Minute` carries no bound to either, and the
     * position is reported as not derivable — so there is nothing to take in. That the inner rule is
     * lost is older than this and is a limit of what a bound is read off, not of the projection.
     * Reported separately; this holds the agreement, and will want the bounds once that is fixed.
     */
    @Test
    void aNewtypeOverANewtypeIsBoundedByNeitherReading() {
        FieldDomains domains = domainsIn("""
                module example.nested

                data Minute = Int
                    invariant withinDay = value >= 0 && value <= 1440

                data StartMinute = Minute
                data EndMinute = Minute

                data Span =
                    { from: StartMinute
                    , to: EndMinute
                    }
                    invariant ordered = from.value < to.value
                """, "Span");

        assertNull(domains.at("from"));
        assertNull(domains.at("to"));
    }

    /**
     * A bound is as read where its type comes from another module as where it is declared.
     *
     * <p>The discharge reading of an imported type has already been settled into the folds its
     * operations are, so a classifier working off that reading calls every imported bound a rule it
     * could not read — and every edge of every imported number stops being one a row is owed. What
     * decides it is the reader that gave the position its bounds, which works off the declaration as
     * written and answers the same either side of a module boundary.
     *
     * <p>The seeding still takes nothing from such a type, so an imported position keeps the bounds
     * its own type gives it and nothing relates it to a sibling. That is a narrowing missed and not
     * an edge invented, which is the direction to miss in.
     */
    @Test
    void anImportedBoundIsReadLikeADeclaredOne() {
        Compilation compilation = Compilation.ofSources(List.of("""
                module example.money exposing ( Amount )

                data Amount = Decimal
                    invariant value >= 0.0m
                """, """
                module example.report

                import example.money ( Amount )

                data Forecast = { total: Amount }
                """), souther.compiler.meta.ModulePath.EMPTY);
        compilation.answerEverything();
        Symbols symbols = compilation.db().ask(new Shapes.Scope("example.report")).value();
        assertNotNull(symbols, "the model did not compile");
        TypeName named = new TypeName("example.report", "Forecast");
        FieldDomains domains = FieldDomains.of(named, (Ast.Data) symbols.get(named), symbols);

        assertTrue(domains.exact("total"),
                "the rule is `value >= 0.0m` wherever it is declared");
        assertNull(domains.at("total"),
                "the seeding reads an imported type in the settled form and takes no bound from it,"
                        + " so the position keeps the one its own type gives it and nothing relates"
                        + " it to a sibling across a module boundary");
    }

    /** A newtype has no siblings, so there is nothing here to project. */
    @Test
    void aNewtypeHasNothingToProjectOnto() {
        assertNull(domainsIn(TIMESHEET, "MinuteOfDay").at("value"));
    }
}
