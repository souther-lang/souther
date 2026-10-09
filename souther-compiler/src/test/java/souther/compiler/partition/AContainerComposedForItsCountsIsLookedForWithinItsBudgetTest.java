package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.carrier.Membership;
import souther.compiler.check.DeclaredSig;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Position;
import souther.compiler.inputs.Quantities;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.meta.ModulePath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.types.Type;

import java.time.Duration;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.SequencedMap;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTimeoutPreemptively;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Composing a container for its counts looks at so many ways of sharing its elements out and no
 * more, and says so where it stopped.
 *
 * <p>The ways of sharing a size out grow with the size and with how many ways an element answers the
 * statements: five groups of elements and sixteen elements are tens of thousands of them. Counts no
 * container meets — more elements above one than above nought — leave none of them building
 * anything, so the walk goes on until something stops it, and what stops it is the figure.
 */
class AContainerComposedForItsCountsIsLookedForWithinItsBudgetTest {

    private static final String SOURCE = """
            module g

            data Ok

            behavior counted : (xs: List<Int>) -> Ok
            """;

    @Test
    void countsNoContainerMeetsStopAtTheSharingsLookedAt() {
        TermRealizations.Realization made = assertTimeoutPreemptively(Duration.ofSeconds(30),
                () -> composed(new long[] {0, 1, 2, 3}, new long[] {3, 4, 5, 6}));
        TermRealizations.Realization.Stopped stopped =
                assertInstanceOf(TermRealizations.Realization.Stopped.class, made,
                        "nothing is built, and the walk was stopped rather than walked out");
        assertTrue(stopped.met().figures().contains(CompositionBudget.SHARES_A_COUNT_IS_TRIED_AT),
                () -> "the sharings looked at are what stopped it: " + stopped.met());
    }

    /**
     * The least count a region of counts holds is one of them where there is one, and that there
     * is none only where the region holds no whole number from nought — never because one could not
     * be named.
     */
    @Test
    void theLeastCountIsOneOfThemOrAProofThereIsNone() {
        CountedElements count = aCount(Optional.empty());
        assertEquals(new CountedElements.Least.At(Count.of(2)),
                count.leastIn(LevelRegion.of(new LevelInterval(Bound.at(level(2), true), null))));
        assertEquals(new CountedElements.Least.At(Count.of(1_000_000_000L)),
                assertTimeoutPreemptively(Duration.ofSeconds(5), () -> count.leastIn(
                        LevelRegion.of(new LevelInterval(Bound.at(level(1_000_000_000L), true),
                                null)))),
                "a count far up is named at once, read off the run and not walked up to");
        assertEquals(new CountedElements.Least.None(),
                count.leastIn(LevelRegion.of(new LevelInterval(Bound.at(level(1), false),
                        Bound.at(level(2), false)))),
                "nothing whole lies strictly between one and two");
        assertEquals(new CountedElements.Least.None(),
                count.leastIn(LevelRegion.of(new LevelInterval(null, Bound.at(level(0), false)))),
                "and no count is below none");
    }

    /**
     * Which count is counted is the container and the statement, whatever a reading worked out
     * about an element meeting it: two readings of one count are one count to gather demands by.
     */
    @Test
    void aCountIsTheSameCountHoweverFarItsStatementWasRead() {
        CountedElements read = aCount(Optional.of(List.of()));
        CountedElements unread = aCount(Optional.empty());
        assertEquals(read.identity(), unread.identity());
    }

    /**
     * Two readings of one count taken together keep what either worked out about an element
     * meeting its statement, and keep the same whichever came first.
     */
    @Test
    void twoReadingsOfOneCountKeepWhatEitherWorkedOutInEitherOrder() {
        Read read = read();
        NumericTerm element = new NumericTerm.ValueOf(read.xs().element());
        TakenConstraint above = new TakenConstraint.Affine(
                new LinearForm<>(ExactRatio.ZERO, Map.of(element, ExactRatio.ONE)), Rel.GT);
        TakenConstraint below = new TakenConstraint.Affine(
                new LinearForm<>(ExactRatio.of(-10), Map.of(element, ExactRatio.ONE)), Rel.LT);
        CountedElements none = aCount(Optional.empty());
        CountedElements one = aCount(Optional.of(List.of(above)));
        CountedElements other = aCount(Optional.of(List.of(below)));

        assertEquals(Optional.of(List.of(above)), none.and(one).anElementMeeting(),
                "what one reading worked out is kept where the other worked out nothing");
        assertEquals(none.and(one).anElementMeeting(), one.and(none).anElementMeeting(),
                "whichever came first");
        assertEquals(Set.of(above, below),
                Set.copyOf(one.and(other).anElementMeeting().orElseThrow()),
                "and where both worked something out, both are kept");
        assertEquals(Set.copyOf(one.and(other).anElementMeeting().orElseThrow()),
                Set.copyOf(other.and(one).anElementMeeting().orElseThrow()),
                "whichever came first");
    }

    private static Level level(long count) {
        return new Level.OfTheQuantity(ExactRatio.of(count));
    }

    /** A count of the elements of {@code xs} above nought. */
    private static CountedElements aCount(Optional<List<TakenConstraint>> anElementMeeting) {
        Read read = read();
        NumericTerm element = new NumericTerm.ValueOf(read.xs().element());
        Proposition meets = new Proposition.Compared(new Relation.Affine(new LinearForm<>(
                ExactRatio.ZERO, Map.of(new DecisionAtom.OfTheInput(element), ExactRatio.ONE)),
                Rel.GT), true);
        return CountedElements.of("counted", new Quantity.HowManyMeet(read.xs(), meets),
                read.measuring(), anElementMeeting);
    }

    /**
     * The container for each count of elements above {@code above[i]} at {@code asked[i]}.
     */
    private static TermRealizations.Realization composed(long[] above, long[] asked) {
        Read read = read();
        Quantities measuring = read.measuring();
        TermPath xs = read.xs();
        NumericTerm element = new NumericTerm.ValueOf(xs.element());

        List<RealizationTarget.ACount> counts = new ArrayList<>();
        SequencedMap<RealizationTarget, AskedAt> demands = new LinkedHashMap<>();
        for (int i = 0; i < above.length; i++) {
            Proposition meets = new Proposition.Compared(new Relation.Affine(new LinearForm<>(
                    ExactRatio.of(-above[i]),
                    Map.of(new DecisionAtom.OfTheInput(element), ExactRatio.ONE)), Rel.GT), true);
            RealizationTarget.ACount count = new RealizationTarget.ACount(CountedElements.of(
                    "counted", new Quantity.HowManyMeet(xs, meets), measuring, Optional.empty()));
            counts.add(count);
            demands.put(count, AskedAt.oneNumberOf(NumbersAskedFor.of(LevelRegion.point(
                    new Level.OfTheQuantity(ExactRatio.of(asked[i])))), Count.of(asked[i])));
        }
        return CardinalityComposer.compose(new Type.ListOf(Type.INT), counts, demands, null,
                List.of(), measuring.region(), read.reading());
    }

    /** The input of {@link #SOURCE}, read: its numbers, its rules and its container. */
    private record Read(Quantities measuring, RuleReadingContext reading, TermPath xs) {}

    private static Read read() {
        Compilation compilation = Compilation.ofSources(List.of(SOURCE), ModulePath.EMPTY);
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Map<String, DeclaredSig> sigs =
                compilation.db().ask(new Bodies.DeclaredSignatures(module)).value();
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        RuleReadingContext reading = RuleReadingContext.unshared(rules, ReadAs.THE_COMPILATION_DOES);
        InputDomain input = InputDomain.of(sigs.get("counted"), reading, Membership.none());
        TermPath xs = input.positions().stream().map(Position::path)
                .filter(each -> each.toString().equals("xs")).findFirst().orElseThrow();
        return new Read(input.quantities(rules), reading, xs);
    }
}
