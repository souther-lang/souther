package souther.compiler.check;

import souther.compiler.ast.Hir;
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
        Hir.Data data = (Hir.Data) symbols.declarations().declaration(named);
        assertNotNull(data, "no `" + type + "` in " + module);
        return FieldDomains.of(named, data, symbols);
    }

    private static void assertBounds(NumericDomain.Bounds bounds, long min, long max) {
        assertNotNull(bounds, "nothing bounds this field");
        assertEquals(0, BigDecimal.valueOf(min).compareTo(souther.compiler.numeric.Count.number(bounds.min().at()).at()),
                "min was " + bounds.min());
        assertEquals(0, BigDecimal.valueOf(max).compareTo(souther.compiler.numeric.Count.number(bounds.max().at()).at()),
                "max was " + bounds.max());
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
        assertTrue(domains.allRulesRead(), "both rules were read");
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

    /**
     * Over decimals a strict rule moves no end and takes the value at one of them away.
     *
     * <p>There is no next value to step onto, so both ends stay where {@code Ratio} put them. What
     * {@code low < high} does is leave {@code low} everything up to 1 without 1 itself, and
     * {@code high} everything from 0 without 0 — which is the whole of the rule and not an
     * approximation of it.
     */
    @Test
    void aStrictRuleOverDecimalsLeavesTheEndsWhereTheyAreAndOutsideTheRange() {
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
        assertTrue(domains.at("low").min().inclusive(), "a low of 0 needs no room under it");
        assertFalse(domains.at("low").max().inclusive(), "a low of 1 leaves no room above it");
        assertFalse(domains.at("high").min().inclusive(), "nor a high of 0 below it");
        assertTrue(domains.at("high").max().inclusive(), "and a high of 1 needs none");
        assertTrue(domains.allRulesRead(), "and every rule of the record was taken into these");
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
        assertFalse(domains.allRulesRead(), "0 is in these bounds and no row can write it");
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
        assertTrue(domains.allRulesRead(), "both rules are comparisons of whole numbers");
    }

    /**
     * A rule that is not a comparison narrows no number and still leaves nothing promised.
     *
     * <p>The pattern says nothing about how many minutes a day has, and the minutes keep their
     * bounds. What it does say is that not every interval can be built, and an edge of the minutes is
     * a whole interval with that edge in it — so whether one can be written is a question the pattern
     * takes part in however plainly the numbers were read.
     */
    @Test
    void aRuleThatIsNotAComparisonLeavesNoEdgePromised() {
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
        assertFalse(domains.allRulesRead(),
                "the pattern narrows no minute, and whether a minute of 1439 can be written is a"
                        + " question about a whole interval, which has a label in it");
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
     * A rule reaches through as many names as are wrapped round the number.
     *
     * <p>`data StartMinute = Minute` is a number the language compares, so it is one the domain
     * carries (#461). Both ends are minutes of a day and the rule between them is read at the atoms
     * they are, so `from` stops where `to` can still be — a name wrapped round a number is not a
     * place a rule stops.
     */
    @Test
    void aRuleReachesThroughAsManyNamesAsAreWrappedRoundTheNumber() {
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

        assertBounds(domains.at("from"), 0, 1439);
        assertBounds(domains.at("to"), 1, 1440);
    }

    /**
     * A bound is as read where its type comes from another module as where it is declared.
     *
     * <p>The discharge reading of an imported type has already been settled into the folds its
     * operations are, so a classifier working off that reading calls every imported bound a rule it
     * could not read — and every edge of every imported number stops being one a row is owed. Held
     * because two things have to line up for it: the bindings a declaration's fields are computed
     * under, which are the declaring module's wherever the declaration is read (#466), and the reader
     * that classifies its rules, which works off the declaration as written.
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
        FieldDomains domains = FieldDomains.of(named, (Hir.Data) symbols.declarations().declaration(named), symbols);

        assertTrue(domains.allRulesRead(),
                "the rule is `value >= 0.0m` wherever it is declared");
        assertEquals(0, BigDecimal.ZERO.compareTo(souther.compiler.numeric.Count.number(domains.at("total").min().at()).at()),
                "and it reaches the domain from there too");
    }

    /**
     * A doubt reaches as far as the bound it is about.
     *
     * <p>`a` has no rule of its own that the domain could not hold. Its upper bound is `b`'s, carried
     * by the equality, and `b` holds a hole the domain cannot keep — so `a = 10` wants the `b` the
     * hole refuses. A bound arrives along a path through the differences, and the doubt takes the
     * same path or it is not about the same bound.
     */
    @Test
    void aBoundReachedThroughAnotherAtomCarriesThatAtomsDoubt() {
        FieldDomains domains = domainsIn("""
                module example.paired

                data N = Int
                    invariant within = value >= 0 && value <= 10

                data R =
                    { a: N
                    , b: N
                    }
                    invariant same = a == b
                    invariant notTen = b.value /= 10
                """, "R");

        assertBounds(domains.at("a"), 0, 10);
        assertFalse(domains.allRulesRead(),
                "a's edge is b's edge, carried by the equality, and b holds a hole this cannot keep");
    }

    /**
     * A relation narrows the same either side of a module boundary.
     *
     * <p>A relation is a projection only where both ends brought their ranges. An imported type's own
     * invariant could not be re-elaborated by the module reading it (#464/#466), so the ordering
     * arrived and the ranges did not — nothing narrowed, the derivation put each type's own edges
     * back, and those are values no pair holds.
     */
    @Test
    void aRelationNarrowsTheSameAcrossAModuleBoundary() {
        Compilation compilation = Compilation.ofSources(List.of("""
                module example.money exposing ( Amount )

                data Amount = Int
                    invariant within = value >= 0 && value <= 10
                """, """
                module example.pair

                import example.money ( Amount )

                data Pair =
                    { a: Amount
                    , b: Amount
                    }
                    invariant ordered = a < b
                """), souther.compiler.meta.ModulePath.EMPTY);
        compilation.answerEverything();
        Symbols symbols = compilation.db().ask(new Shapes.Scope("example.pair")).value();
        TypeName named = new TypeName("example.pair", "Pair");
        FieldDomains domains = FieldDomains.of(named, (Hir.Data) symbols.declarations().declaration(named), symbols);

        assertBounds(domains.at("a"), 0, 9);
        assertBounds(domains.at("b"), 1, 10);
        assertTrue(domains.allRulesRead());
    }

    /**
     * A rule reaches as far as the construction it can refuse, which is further than a report looks.
     *
     * <p>The walk that takes a value apart for measuring stops two levels down, because past that a
     * report is no longer about anything the author recognises as one input. A rule four records down
     * refuses the outermost construction exactly as one on its own fields does, so the question of
     * whether a row can be written at all cannot borrow that limit.
     */
    @Test
    void aRuleBelowTheDepthAReportLooksAtStillRefusesTheValue() {
        FieldDomains domains = domainsIn("""
                module example.deep

                data N = Int
                    invariant within = value >= 0 && value <= 10

                data Leaf =
                    { x: N
                    , tag: String
                    }
                    invariant tagged = String.matches("[a-z]+", tag)

                data L2 = { leaf: Leaf }
                data L1 = { l2: L2 }

                data Root =
                    { n: N
                    , l1: L1
                    }
                """, "Root");

        assertBounds(domains.at("n"), 0, 10);
        assertFalse(domains.allRulesRead(),
                "the pattern is three records down and a Root cannot be built without going through"
                        + " it");
    }

    /** And not through what a construction need not make. A rule inside an optional is a rule about a
     * value that can be left out, so it refuses nothing here. */
    @Test
    void aRuleInsideSomethingOptionalRefusesNothing() {
        FieldDomains domains = domainsIn("""
                module example.optional

                data N = Int
                    invariant within = value >= 0 && value <= 10

                data Note =
                    { tag: String }
                    invariant tagged = String.matches("[a-z]+", tag)

                data Root =
                    { n: N
                    , note: Note?
                    , others: List<Note>
                    }
                """, "Root");

        assertBounds(domains.at("n"), 0, 10);
        assertTrue(domains.allRulesRead(),
                "a Root with no note and no others is a Root, and the pattern never runs");
    }

    /**
     * And the same where the reader has a declaration of that spelling itself.
     *
     * <p>Four ways reach another module's declaration and the bindings were wrong for all of them
     * (#466). This is the one that would survive any repair answering from a bare name: two
     * declarations of one spelling sharing a binding is a field standing for two values.
     */
    @Test
    void aRelationNarrowsWhereTheReaderHasThatSpellingToo() {
        Compilation compilation = Compilation.ofSources(List.of("""
                module example.money exposing ( Amount )

                data Amount = Int
                    invariant within = value >= 0 && value <= 10
                """, """
                module example.report

                import example.money as M

                data Amount = String
                    invariant named = String.length(value) >= 1

                data Pair =
                    { a: M.Amount
                    , b: M.Amount
                    }
                    invariant ordered = a < b
                """), souther.compiler.meta.ModulePath.EMPTY);
        compilation.answerEverything();
        Symbols symbols = compilation.db().ask(new Shapes.Scope("example.report")).value();
        TypeName named = new TypeName("example.report", "Pair");
        FieldDomains domains = FieldDomains.of(named, (Hir.Data) symbols.declarations().declaration(named), symbols);

        assertBounds(domains.at("a"), 0, 9);
        assertBounds(domains.at("b"), 1, 10);
        assertTrue(domains.allRulesRead(),
                "a local `Amount` of another shape says nothing about the one these fields are");
    }

    /** A newtype has no siblings, so there is nothing here to project. */
    @Test
    void aNewtypeHasNothingToProjectOnto() {
        assertNull(domainsIn(TIMESHEET, "MinuteOfDay").at("value"));
    }
}
