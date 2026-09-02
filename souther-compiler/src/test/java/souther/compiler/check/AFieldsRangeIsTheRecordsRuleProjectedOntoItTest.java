package souther.compiler.check;

import souther.compiler.query.Scopes;
import souther.compiler.ast.Hir;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.query.Compilation;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;
import souther.compiler.types.TypeSymbol;

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
        Symbols symbols = Scopes.derived(compilation.db(), module).value();
        assertNotNull(symbols, "the model did not compile");
        TypeSymbol.AtModule named = TypeSymbols.declared(new TypeKey(module, type));
        Hir.Data data = (Hir.Data) symbols.declaredNode(named.key());
        assertNotNull(data, "no `" + type + "` in " + module);
        return FieldDomains.of(named, data, symbols, souther.compiler.query.ReadAs.THE_COMPILATION_DOES);
    }

    /** What the rules leave the field the record's own clauses call {@code field}. */
    private static NarrowedBounds at(FieldDomains domains, String field) {
        return domains.at(RuleKey.of(field));
    }

    private static void assertBounds(NarrowedBounds narrowed, long min, long max) {
        NumericDomain.Bounds bounds = narrowed.bounds();
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

        assertBounds(at(domains, "startsAt"), 0, 1439);
        assertBounds(at(domains, "endsAt"), 1, 1440);
        assertTrue(domains.projection().isCertified(), "both rules were read");
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

        assertBounds(at(domains, "startsAt"), 0, 1440);
        assertBounds(at(domains, "endsAt"), 0, 1440);
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

        assertBounds(at(domains, "worked"), 0, 24);
        assertBounds(at(domains, "lateNight"), 0, 24);
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

        assertBounds(at(domains, "low"), 0, 1);
        assertBounds(at(domains, "high"), 0, 1);
        assertTrue(at(domains, "low").bounds().min().inclusive(), "a low of 0 needs no room under it");
        assertFalse(at(domains, "low").bounds().max().inclusive(),
                "a low of 1 leaves no room above it");
        assertFalse(at(domains, "high").bounds().min().inclusive(), "nor a high of 0 below it");
        assertTrue(at(domains, "high").bounds().max().inclusive(), "and a high of 1 needs none");
        assertTrue(domains.projection().isCertified(), "and every rule of the record was taken into these");
    }

    /**
     * A rule that skips a value at the edge of a range moves the edge; a range is all the domain
     * hands over, and an edge is somewhere a range can go.
     *
     * <p>Which side of the hole the value lies is not something the rule says on its own — it is
     * something the type's own bound says, and the two together leave the field at one or above.
     * With the edge moved there is nothing left over: every value the range holds is one a row can
     * write, which is what makes the projection exact rather than merely sound.
     */
    @Test
    void aRuleThatSkipsAValueAtTheEdgeMovesTheEdge() {
        FieldDomains domains = domainsIn("""
                module example.skip

                data N = Int
                    invariant within = value >= 0 && value <= 10

                data R =
                    { a: N
                    }
                    invariant nonzero = a.value /= 0
                """, "R");

        assertBounds(at(domains, "a"), 1, 10);
        assertTrue(domains.projection().isCertified(),
                "and the range is now the whole of it: every value in it is one a row can write");
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

        assertBounds(at(domains, "startsAt"), 2, 1439);
        assertTrue(domains.projection().isCertified(), "both rules are comparisons of whole numbers");
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

        assertBounds(at(domains, "startsAt"), 0, 1439);
        assertFalse(domains.projection().isCertified(),
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

        assertNull(at(domains, "note").bounds(), "a string has no numbers to bound");
        assertNull(at(domains, "count").bounds(),
                "an Int the model draws no line through is unbounded");
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

        assertBounds(at(domains, "from"), 0, 1439);
        assertBounds(at(domains, "to"), 1, 1440);
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
        Symbols symbols = Scopes.derived(compilation.db(), "example.report").value();
        assertNotNull(symbols, "the model did not compile");
        TypeSymbol.AtModule named = TypeSymbols.declared(new TypeKey("example.report", "Forecast"));
        FieldDomains domains = FieldDomains.of(named, (Hir.Data) symbols.declaredNode(named.key()), symbols, souther.compiler.query.ReadAs.THE_COMPILATION_DOES);

        assertTrue(domains.projection().isCertified(),
                "the rule is `value >= 0.0m` wherever it is declared");
        assertEquals(0, BigDecimal.ZERO.compareTo(
                        souther.compiler.numeric.Count.number(
                                at(domains, "total").bounds().min().at()).at()),
                "and it reaches the domain from there too");
    }

    /**
     * A doubt reaches as far as the bound it is about.
     *
     * <p>`a` has no rule of its own beyond its type's. Its upper bound is `b`'s, carried by the
     * equality — and `b`'s own upper bound is ten with ten held away from it, which leaves `b` at
     * nine. So `a` is at nine as well: the hole moved `b`'s edge and the equality carried the edge,
     * rather than leaving ten in `a`'s range with a note that something about it was doubtful.
     */
    @Test
    void aBoundReachedThroughAnotherAtomTakesThatAtomsMovedEdge() {
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

        assertBounds(at(domains, "a"), 0, 9);
        assertTrue(domains.projection().isCertified(),
                "and nothing is left over: `a = 9` is written with `b = 9`, which the hole admits");
    }

    /**
     * An edge the rules put at a value no decimal writes is handed over rounded past it, and the
     * reading says so.
     *
     * <p>{@code 3 * value <= 1} leaves the field at a third, and a third does not terminate — no
     * decimal a model writes is one. The reasoning reaches the edge exactly; the number standing for
     * it is a hair outside. That is not a rule the range failed to state, so it is its own cause: a
     * reader placing a row at this edge is being given an edge the rules did not draw.
     */
    @Test
    void anEdgeNoDecimalWritesIsSaidToBeRounded() {
        FieldDomains domains = domainsIn("""
                module example.third

                data D = Decimal
                    invariant atLeastNone = value >= 0.0m
                    invariant aThird = 3.0m * value <= 1.0m

                data R =
                    { d: D
                    }
                """, "R");

        assertTrue(domains.projection() instanceof ProjectionEvidence.NotCertified approximate
                        && approximate.causes().stream()
                                .anyMatch(cause -> cause instanceof ProjectionEvidence.Cause.Rounded),
                "the edge is a third and no decimal is: " + domains.projection());
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
        Symbols symbols = Scopes.derived(compilation.db(), "example.pair").value();
        TypeSymbol.AtModule named = TypeSymbols.declared(new TypeKey("example.pair", "Pair"));
        FieldDomains domains = FieldDomains.of(named, (Hir.Data) symbols.declaredNode(named.key()), symbols, souther.compiler.query.ReadAs.THE_COMPILATION_DOES);

        assertBounds(at(domains, "a"), 0, 9);
        assertBounds(at(domains, "b"), 1, 10);
        assertTrue(domains.projection().isCertified());
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

        assertBounds(at(domains, "n"), 0, 10);
        assertFalse(domains.projection().isCertified(),
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

        assertBounds(at(domains, "n"), 0, 10);
        assertTrue(domains.projection().isCertified(),
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
        Symbols symbols = Scopes.derived(compilation.db(), "example.report").value();
        TypeSymbol.AtModule named = TypeSymbols.declared(new TypeKey("example.report", "Pair"));
        FieldDomains domains = FieldDomains.of(named, (Hir.Data) symbols.declaredNode(named.key()), symbols, souther.compiler.query.ReadAs.THE_COMPILATION_DOES);

        assertBounds(at(domains, "a"), 0, 9);
        assertBounds(at(domains, "b"), 1, 10);
        assertTrue(domains.projection().isCertified(),
                "a local `Amount` of another shape says nothing about the one these fields are");
    }

    /** A newtype has no siblings, so there is nothing here to project. */
    @Test
    void aNewtypeHasNothingToProjectOnto() {
        assertNull(at(domainsIn(TIMESHEET, "MinuteOfDay"), "value").bounds());
    }
}
