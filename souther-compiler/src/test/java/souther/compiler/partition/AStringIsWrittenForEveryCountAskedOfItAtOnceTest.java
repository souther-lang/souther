package souther.compiler.partition;

import net.unit8.notation199x.pattern.CodePoints;
import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.ast.Hir;
import souther.compiler.check.Carrier;
import souther.compiler.check.ReadingPolicy;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.ScopedDeclarations;
import souther.compiler.check.Symbols;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermOrdersFixtures;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.semantics.CodePointClass;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;
import souther.compiler.values.AsACompilationAllows;
import souther.runtime.Strings;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.SequencedMap;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * The counts of one string's code points and how long it is are tied to each other, and a string
 * is written for all of them at once or for none.
 *
 * <p>Two classes count the code points they share in both, none holds more than the string is
 * long, and a class that leaves a whitespace separator out leaves nothing out. A string
 * written for each number alone and put side by side would answer none of them, so what is held
 * here is that what is offered reads back as every number — and that a group no string answers is
 * told apart from a group this compiler did not look in.
 */
class AStringIsWrittenForEveryCountAskedOfItAtOnceTest {

    private static final Symbols SYMBOLS = Symbols.none(DefaultStdlib.get());
    private static final RuleReadingSource RULES = RuleReadings.ofNoClauseFiled(SYMBOLS);
    private static final ReadingPolicy POLICY = new ReadingPolicy(64, 12,
            AsACompilationAllows.admittedValues(), AsACompilationAllows.whatARuleLeaves());
    private static final RuleReadingContext READING = RuleReadingContext.unshared(RULES, POLICY);
    private static final TermPath AT = TermPath.of("t");

    private static final NumericTerm.CodePointClassCount NOT_WHITESPACE =
            counting(new CodePointClass.NotWhitespace());
    private static final NumericTerm.CodePointClassCount NOT_WHITESPACE_NOR_COMMA =
            counting(new CodePointClass.NotWhitespaceNorEqualTo(','));
    private static final NumericTerm.CodePointClassCount NOT_WHITESPACE_NOR_SPACE =
            counting(new CodePointClass.NotWhitespaceNorEqualTo(' '));
    private static final NumericTerm LENGTH = NumericTerm.TakenOf.asItStands(
            ValueName.Stdlib.operation("String", "length"), AT, Type.STRING,
            ScopedDeclarations.wrapsOf(SYMBOLS), SYMBOLS);
    private static final NumericTerm SUM = NumericTerm.CodePointValueSum.of(AT, Type.STRING,
            ScopedDeclarations.wrapsOf(SYMBOLS));

    private static NumericTerm.CodePointClassCount counting(CodePointClass counted) {
        return NumericTerm.CodePointClassCount.of(AT, counted, Type.STRING,
                ScopedDeclarations.wrapsOf(SYMBOLS));
    }

    /** What each number is asked to be: one value, or anything but those. */
    private static final class Demands {

        private final SequencedMap<RealizationTarget, AskedAt> asked = new LinkedHashMap<>();
        private final Map<RealizationTarget.OfANumber, Carrier> measured = new LinkedHashMap<>();

        Demands exactly(NumericTerm term, long number) {
            return holding(term, new NumericSet.At(Count.of(number)));
        }

        Demands notNought(NumericTerm term) {
            return holding(term, new NumericSet.AwayFrom(List.of(Count.of(0))));
        }

        private Demands holding(NumericTerm term, NumericSet set) {
            RealizationTarget.OfANumber target = RealizationTarget.of(term);
            asked.put(target, AskedAt.theClass(set, Carrier.WHOLE));
            measured.put(target, TermOrdersFixtures.at(term, Type.STRING, SYMBOLS).answered());
            return this;
        }

        TermRealizations.Realization written() {
            return TermRealizations.stringsHoldingTheirNumbers(measured, Type.STRING, asked, null,
                    READING);
        }
    }

    /** What a string is read back as, by the run time's own reading of it. */
    private static List<String> offered(TermRealizations.Realization made) {
        TermRealizations.Realization.Built built = assertInstanceOf(
                TermRealizations.Realization.Built.class, made, () -> "nothing was written: " + made);
        List<String> out = new ArrayList<>();
        built.values().forEach(each -> out.add(
                assertInstanceOf(Hir.StringLit.class, each.value()).value()));
        return out;
    }

    private static long notWhitespaceIn(String text) {
        return text.codePoints().filter(new CodePointClass.NotWhitespace()::contains).count();
    }

    private static long notWhitespaceNorCommaIn(String text) {
        return text.codePoints()
                .filter(new CodePointClass.NotWhitespaceNorEqualTo(',')::contains).count();
    }

    private static long lengthOf(String text) {
        return text.codePointCount(0, text.length());
    }

    /** Both classes and the length, each at its own number, which only a string with some of each
     *  kind of code point answers. */
    @Test
    void aStringIsWrittenWhoseCountsAreAllThoseAsked() {
        assertNotNull(LENGTH);
        List<String> strings = offered(new Demands()
                .exactly(NOT_WHITESPACE_NOR_COMMA, 2)
                .exactly(NOT_WHITESPACE, 3)
                .exactly(LENGTH, 5).written());
        assertEquals(true, !strings.isEmpty());
        for (String each : strings) {
            assertEquals(2, notWhitespaceNorCommaIn(each), each);
            assertEquals(3, notWhitespaceIn(each), each);
            assertEquals(5, lengthOf(each), each);
        }
    }

    /**
     * A class that is a set of code points, the space among them, is counted beside the code
     * points that are not whitespace and the length: what it shares with each is counted in
     * both, so a string answering all three is written with code points told apart by every one
     * of them — whitespace in the set and out of it among them.
     */
    @Test
    void aStringIsWrittenWhoseCountsAreAllThoseAskedOfASetHoldingWhitespace() {
        CodePointClass set = CodePointClass.of(CodePoints.between('a', 'z')
                .or(CodePoints.between('0', '9')).or(CodePoints.of(' ')));
        List<String> strings = offered(new Demands()
                .exactly(counting(set), 2)
                .exactly(NOT_WHITESPACE, 3)
                .exactly(LENGTH, 5).written());
        assertEquals(true, !strings.isEmpty());
        for (String each : strings) {
            assertEquals(2, each.codePoints().filter(set::contains).count(), each);
            assertEquals(3, notWhitespaceIn(each), each);
            assertEquals(5, lengthOf(each), each);
        }
    }

    /**
     * A string is written for any number of separators a model sets apart, among them the ones a
     * plain letter would be taken from: the letter that stands for the rest is chosen from outside
     * all of them rather than from a list they can cover.
     */
    @Test
    void aStringIsWrittenWhateverSeparatorsAreSetApart() {
        List<NumericTerm.CodePointClassCount> classes = new ArrayList<>();
        for (char each : new char[] {'x', 'y', 'z', 'a'}) {
            classes.add(counting(new CodePointClass.NotWhitespaceNorEqualTo(each)));
        }
        Demands demands = new Demands();
        for (NumericTerm.CodePointClassCount each : classes) {
            demands.exactly(each, 3);
        }
        List<String> strings = offered(demands.exactly(NOT_WHITESPACE, 4).written());
        assertEquals(true, !strings.isEmpty());
        for (String each : strings) {
            assertEquals(4, notWhitespaceIn(each), each);
            for (NumericTerm.CodePointClassCount counted : classes) {
                assertEquals(3, each.codePoints().filter(counted.counted()::contains).count(), each);
            }
        }
    }

    /**
     * A separator that combines with the code point before it: a letter and the mark are one code
     * point once the text is let in. Two code points not whitespace, one of them not the mark, and
     * two long is a string that exists — an ideograph and the mark — and the one written with a
     * letter is not it, so what is offered is what the text reads as and not what was laid out.
     */
    @Test
    void aStringIsOfferedAsTheLanguageHoldsItWhereASeparatorCombines() {
        int mark = 0x0307;
        NumericTerm.CodePointClassCount apart = counting(new CodePointClass.NotWhitespaceNorEqualTo(mark));
        String composed = Strings.admit("ẋ");
        assertEquals(1, composed.codePointCount(0, composed.length()),
                "a letter and the mark are one code point as held");

        List<String> strings = offered(new Demands()
                .exactly(NOT_WHITESPACE, 2)
                .exactly(apart, 1)
                .exactly(LENGTH, 2).written());
        assertEquals(true, !strings.isEmpty());
        for (String each : strings) {
            assertEquals(each, Strings.admit(each), "offered as held");
            assertEquals(2, notWhitespaceIn(each), each);
            assertEquals(1, each.codePoints().filter(apart.counted()::contains).count(), each);
            assertEquals(2, lengthOf(each), each);
        }
    }

    /** A separator that is half of a surrogate pair is no code point a string holds. */
    @Test
    void aLoneSurrogateIsNoSeparator() {
        assertThrows(IllegalArgumentException.class,
                () -> new CodePointClass.NotWhitespaceNorEqualTo(0xD800));
    }

    /** One of nought and the other not, which is a string of nothing but separators. */
    @Test
    void aStringOfSeparatorsAloneAnswersAClassOfNoneAndAClassOfSome() {
        List<String> strings = offered(new Demands()
                .exactly(NOT_WHITESPACE_NOR_COMMA, 0)
                .notNought(NOT_WHITESPACE)
                .exactly(LENGTH, 3).written());
        for (String each : strings) {
            assertEquals(0, notWhitespaceNorCommaIn(each), each);
            assertEquals(true, notWhitespaceIn(each) >= 1, each);
            assertEquals(3, lengthOf(each), each);
            assertEquals(true, each.contains(","), each);
        }
    }

    /** More code points of a class than there are that are not whitespace is no string. */
    @Test
    void aClassHoldingMoreThanTheCodePointsThatAreNotWhitespaceHasNoString() {
        assertInstanceOf(TermRealizations.Realization.None.class, new Demands()
                .exactly(NOT_WHITESPACE_NOR_COMMA, 3)
                .exactly(NOT_WHITESPACE, 2).written());
    }

    /** Or more than the string is long. */
    @Test
    void aClassHoldingMoreThanTheStringIsLongHasNoString() {
        assertInstanceOf(TermRealizations.Realization.None.class, new Demands()
                .exactly(NOT_WHITESPACE, 3)
                .exactly(LENGTH, 2).written());
    }

    /** A separator that is whitespace leaves nothing out of what is not whitespace. */
    @Test
    void aClassLeavingOutWhitespaceCountsWhatTheOtherDoes() {
        assertInstanceOf(TermRealizations.Realization.None.class, new Demands()
                .exactly(NOT_WHITESPACE_NOR_SPACE, 1)
                .exactly(NOT_WHITESPACE, 2).written());
        List<String> strings = offered(new Demands()
                .exactly(NOT_WHITESPACE_NOR_SPACE, 2)
                .exactly(NOT_WHITESPACE, 2).written());
        for (String each : strings) {
            assertEquals(2, notWhitespaceIn(each), each);
        }
    }

    /**
     * A number past what is searched in full is a string offered where one was found and not a
     * string said not to exist where none was.
     */
    @Test
    void whatWasNotLookedInIsNotSaidToHoldNothing() {
        List<String> strings = offered(new Demands()
                .exactly(NOT_WHITESPACE_NOR_COMMA, 30)
                .exactly(NOT_WHITESPACE, 30)
                .exactly(LENGTH, 40).written());
        for (String each : strings) {
            assertEquals(30, notWhitespaceNorCommaIn(each), each);
            assertEquals(40, lengthOf(each), each);
        }
        TermRealizations.Realization impossible = new Demands()
                .exactly(NOT_WHITESPACE_NOR_COMMA, 30)
                .exactly(NOT_WHITESPACE, 20).written();
        TermRealizations.Realization.Stopped stopped = assertInstanceOf(
                TermRealizations.Realization.Stopped.class, impossible,
                "no string answers it, which this did not search far enough to say");
        assertEquals(Set.of(CompositionBudget.CODE_POINTS_A_STRING_IS_SEARCHED_IN_FULL),
                stopped.met().figures(), "and it says which figure it stopped at");
    }

    /**
     * What the code points come to beside how many of them there are and how many are not
     * whitespace: the counts choose the string's kinds of code point, and the sum is reached by
     * which code points of each kind are written, so every number reads back off one string.
     */
    @Test
    void aStringIsWrittenWhoseCodePointsComeToTheSumBesideItsCounts() {
        for (long sum : new long[] {32 * 3 + 97, 300, 3 * 0x4E00, 0x10FFFF + 2 * 32}) {
            List<String> strings = offered(new Demands()
                    .exactly(SUM, sum)
                    .exactly(NOT_WHITESPACE, 1)
                    .exactly(LENGTH, 3).written());
            for (String each : strings) {
                assertEquals(sum, sumOf(each), each);
                assertEquals(1, notWhitespaceIn(each), each);
                assertEquals(3, lengthOf(each), each);
            }
        }
    }

    /**
     * A sum is no count, and the counts of a string do not decide it: a sum asked alone is not read
     * as a length to write the string at. A million is one code point, and the strings offered
     * beside that one are no longer than a string is searched for in full, and not a million.
     */
    @Test
    void aSumAskedAloneIsNotReadAsALength() {
        List<String> strings = offered(new Demands().exactly(SUM, 1_000_000).written());
        for (String each : strings) {
            assertEquals(1_000_000, sumOf(each), each);
            assertEquals(true, lengthOf(each)
                    <= CompositionBudget.CODE_POINTS_A_STRING_IS_SEARCHED_IN_FULL.maximum(), each);
        }
        assertEquals(true, strings.stream().anyMatch(each -> lengthOf(each) == 1),
                strings::toString);
    }

    /**
     * Which code points of a kind are written is a few of the ones it has, so a sum nothing moved
     * reaches is a string this did not write and never a string said not to exist — even where none
     * does, as no one code point is a surrogate and nothing of none comes to five.
     */
    @Test
    void aSumNothingMovedReachesIsNotSaidToHaveNoString() {
        for (Demands unreached : List.of(
                new Demands().exactly(SUM, 0xD800).exactly(LENGTH, 1),
                new Demands().exactly(SUM, 5).exactly(LENGTH, 0),
                new Demands().exactly(SUM, 5).exactly(NOT_WHITESPACE, 3).exactly(LENGTH, 3))) {
            TermRealizations.Realization made = unreached.written();
            assertEquals(false, made instanceof TermRealizations.Realization.None, made::toString);
            assertEquals(false, made instanceof TermRealizations.Realization.Built,
                    made::toString);
        }
    }

    /** A sum more code points than a string is searched for come to is said as that figure. */
    @Test
    void aSumPastWhatAStringIsSearchedForIsSaidAsTheFigure() {
        TermRealizations.Realization.Stopped stopped = assertInstanceOf(
                TermRealizations.Realization.Stopped.class,
                new Demands().exactly(SUM, 3_000_000_000L).written());
        assertEquals(Set.of(CompositionBudget.CODE_POINTS_A_STRING_IS_SEARCHED_IN_FULL),
                stopped.met().figures());
    }

    private static long sumOf(String text) {
        return text.codePoints().asLongStream().sum();
    }
}
