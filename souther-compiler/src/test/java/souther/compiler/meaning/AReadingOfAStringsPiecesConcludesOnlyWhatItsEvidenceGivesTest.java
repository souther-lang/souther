package souther.compiler.meaning;

import net.unit8.notation199x.pattern.CodePoints;
import net.unit8.notation199x.pattern.PatternMachine;
import net.unit8.notation199x.pattern.PatternMeaning;
import net.unit8.notation199x.pattern.PatternParser;
import net.unit8.notation199x.pattern.PatternRead;
import net.unit8.notation199x.pattern.StringPattern;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;

import souther.compiler.DefaultStdlib;
import souther.compiler.check.DefaultBoundOperationFacts;
import souther.compiler.check.ScopedDeclarations;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.core.WhatABodyReads;
import souther.compiler.diag.SourcePos;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.semantics.CodePointClass;
import souther.compiler.semantics.LawNumber;
import souther.compiler.semantics.LawProposition;
import souther.compiler.semantics.LawSubject;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.OptionalInt;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A reading of some piece of a string, and of some element of a container that comes out the same
 * for every one, concludes what its own parts give and is refused anything else: what a pattern
 * says of a character is what the pattern accepts, what the string's pieces hold is counted of
 * that string by that set, and a value said to be written without the element is one that reads
 * none of it.
 */
class AReadingOfAStringsPiecesConcludesOnlyWhatItsEvidenceGivesTest {

    private static final Symbols SYMBOLS = Symbols.none(DefaultStdlib.get());
    private static final TermPath TITLE = TermPath.of("title");
    private static final TermPath OTHER = TermPath.of("other");
    private static final CodePoints LOWER = CodePoints.between('a', 'z');
    private static final SourcePos POS = new SourcePos(1, 1);

    private static final ValueName.Stdlib CHARACTERS =
            ValueName.Stdlib.operation("String", "characters");
    /** A call taking the characters of the string at {@code TITLE}. */
    private static final Derivation.TheCall SPLIT = new Derivation.TheCall(CHARACTERS,
            Map.of(DefaultBoundOperationFacts.get().piecesOf(CHARACTERS).string(), TITLE));

    private static NumericTerm.CodePointClassCount counting(TermPath of, CodePointClass counted) {
        return NumericTerm.CodePointClassCount.of(of, counted, Type.STRING,
                ScopedDeclarations.wrapsOf(SYMBOLS));
    }

    /**
     * The string {@code CHARACTERS} parts read as holding one of {@code stated}, the way a law's
     * comparison is read: its number read as how many of {@code counted} the string at
     * {@code of} holds.
     */
    private static Optional<Derivation> holding(CodePointClass stated, TermPath of,
                                                CodePointClass counted) {
        LawProposition.Compared<?> law = assertInstanceOf(LawProposition.Compared.class,
                Derivation.SomePieceMeeting.heldBy(CHARACTERS, stated.held()));
        LawNumber<?> number = law.form().coefs().keySet().iterator().next();
        return Optional.of(Derivation.ALawComparison.of(law, Map.of(number,
                        LinearForm.atom(new DecisionAtom.OfTheInput(counting(of, counted)))),
                Map.of(), List.of(), 1));
    }

    /** A character read as matching {@code [a-z]}, {@code within} statements about some piece. */
    private static Derivation aLowerCaseLetter(int within) {
        return new Derivation.ACharacterInAClass(new PatternMeaning.Symbols(LOWER), within);
    }

    @Test
    void someCharacterIsCountedOfItsOwnStringByTheSetItWasReadAs() {
        CodePointClass lower = CodePointClass.of(LOWER);
        Derivation.SomePieceMeeting met = new Derivation.SomePieceMeeting(SPLIT,
                OptionalInt.empty(), 0, holding(lower, TITLE, lower), aLowerCaseLetter(0));
        assertEquals(new Proposition.Compared(new Relation.Affine(LinearForm.<Quantity>atom(
                        new DecisionAtom.OfTheInput(counting(TITLE, lower))), Rel.GT), true),
                met.concludes(Optional.empty()));
        CodePointClass notWhitespace = new CodePointClass.NotWhitespace();
        assertThrows(IllegalArgumentException.class, () -> new Derivation.SomePieceMeeting(
                SPLIT, OptionalInt.empty(), 0,
                holding(notWhitespace, TITLE, notWhitespace), aLowerCaseLetter(0)),
                "another class of the same string");
        assertThrows(IllegalArgumentException.class, () -> new Derivation.SomePieceMeeting(
                SPLIT, OptionalInt.empty(), 0, holding(lower, TITLE, notWhitespace),
                aLowerCaseLetter(0)), "the class stated, counted as another");
        assertThrows(IllegalArgumentException.class, () -> new Derivation.SomePieceMeeting(
                SPLIT, OptionalInt.empty(), 0, holding(lower, OTHER, lower),
                aLowerCaseLetter(0)), "the same class of another string");
        assertThrows(IllegalArgumentException.class, () -> new Derivation.SomePieceMeeting(
                SPLIT, OptionalInt.empty(), 0, Optional.empty(), aLowerCaseLetter(0)),
                "no reading where a character can meet it");
        assertThrows(IllegalArgumentException.class, () -> new Derivation.SomePieceMeeting(
                SPLIT, OptionalInt.of(','), 0, holding(lower, TITLE, lower), aLowerCaseLetter(0)),
                "a split piece is read only as holding a code point that is not whitespace");
    }

    /**
     * What is read of the character of one statement about some character is no reading of the
     * character of another: the statement read inside it is about a piece of its own.
     */
    @Test
    void aCharacterOfAnotherStatementIsNoCharacterOfThisOne() {
        CodePointClass lower = CodePointClass.of(LOWER);
        assertThrows(IllegalArgumentException.class, () -> new Derivation.SomePieceMeeting(
                SPLIT, OptionalInt.empty(), 1, holding(lower, TITLE, lower), aLowerCaseLetter(0)),
                "the character of the statement this one is read inside of");
        assertThrows(IllegalArgumentException.class, () -> new Derivation.SomePieceMeeting(
                SPLIT, OptionalInt.empty(), 0, holding(lower, TITLE, lower), aLowerCaseLetter(1)),
                "the character of a statement read inside this one");
    }

    /**
     * A value is said to be written without the element only by the walk that found it reading
     * the element nowhere: one that reads it, even inside another value, gets no such answer.
     */
    @Test
    void aValueIsSaidToBeWrittenWithoutTheElementOnlyWhereItReadsNoneOfIt() {
        BindingOwner owner = new BindingOwner.OfValue("demo", "f");
        BindingId element = new BindingId(owner, 0);
        BindingId other = new BindingId(owner, 1);
        Core readsOther = new Core.Read("t", other, Type.STRING, POS);
        Core readsElement = new Core.Read("c", element, Type.STRING, POS);
        Core both = new Core.ListLit(List.of(readsOther, readsElement), Type.STRING, POS);
        assertEquals(element, WhatABodyReads.without(readsOther, element).orElseThrow()
                .binding());
        assertTrue(WhatABodyReads.without(readsElement, element).isEmpty());
        assertTrue(WhatABodyReads.without(both, element).isEmpty());
    }

    @Test
    void whatTurnsOnTheElementIsNotSaidToSettle() {
        LawProposition.SomeElement<String> some = new LawProposition.SomeElement<>("xs",
                new LawProposition.Always<>(true), true);
        assertThrows(IllegalArgumentException.class, () -> new Derivation.EveryElementMeetsIt(
                some, aLowerCaseLetter(0), new Derivation.WrittenOut(true),
                new Derivation.EveryElementMeetsIt.Alike.Settled()));
    }

    /**
     * A statement an operation keeps is read of what the operation was handed, and a reading that
     * is no reading of that statement — a value settled on its own — is not taken for one.
     */
    @Test
    void whatAnOperationKeepsIsReadOfWhatItWasHandedAndOfNothingElse() {
        LawProposition.Compared<String> holdsOne = new LawProposition.Compared<>(
                new LinearForm<>(ExactRatio.of(-1), Map.of(new LawNumber.CodePointsOf<>(
                        new LawSubject.Argument<>("s"), new CodePointClass.NotWhitespace()),
                        ExactRatio.ONE)), Rel.GE);
        assertThrows(IllegalArgumentException.class, () ->
                new Derivation.WhereAnOperationKeepsIt(holdsOne,
                        ValueName.Stdlib.operation("String", "lowercase"),
                        new Derivation.WrittenOut(true)));
    }

    /**
     * What a pattern is read as accepting of a string of one code point is what the run time's
     * matcher accepts, over patterns that choose, follow one another, repeat and take nothing.
     */
    @Test
    void theCodePointsAPatternIsReadAsAcceptingAloneAreTheOnesTheRunTimeMatches() {
        List<String> patterns = List.of("[a-z0-9]", "[^a-z]", "a|[0-9]", "ab", "a?b?",
                "(ab)?c", "a*", "a+", "a{2}", "a{0,1}b{0,1}", "x?[a-c]y?", "(|a)", "(a|)b",
                "\\d", "\\s", "[a-z]{1,3}", "(a|bc)", "a{0}");
        List<Integer> asked = new ArrayList<>();
        for (int codePoint = 0; codePoint < 0x300; codePoint++) {
            asked.add(codePoint);
        }
        asked.addAll(List.of(0x2028, 0x2029, 0x3000, 0x4E00, 0x1F600));
        List<String> wrong = new ArrayList<>();
        for (String written : patterns) {
            PatternMeaning meaning = assertInstanceOf(PatternRead.Read.class,
                    PatternParser.read(written), written).meaning();
            CodePoints alone = Derivation.ACharacterInAClass.alone(meaning);
            StringPattern runs = PatternMachine.of(meaning).pattern();
            for (int codePoint : asked) {
                if (alone.has(codePoint) != runs.matches(Character.toString(codePoint))) {
                    wrong.add(written + " at U+" + Integer.toHexString(codePoint));
                }
            }
        }
        assertEquals(List.of(), wrong);
    }

    /**
     * The code points many classes tell apart are as many as the runs they are written with make,
     * and not one for each way of being in or out of each: forty classes, each a run of its own
     * overlapping the next, are told apart into no more than the runs between their ends.
     */
    @Test
    @Timeout(value = 10, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    void manyClassesAreToldApartIntoNoMoreThanTheRunsTheyAreWrittenWith() {
        List<CodePoints> classes = new ArrayList<>();
        for (int at = 0; at < 40; at++) {
            classes.add(CodePoints.between(0x100 + at * 4, 0x100 + at * 4 + 9));
        }
        List<CodePoints> alike = CodePointClass.toldApart(classes);
        int ends = 0;
        for (CodePoints each : classes) {
            ends += 2 * each.ranges().size();
        }
        assertTrue(alike.size() <= ends + 2, alike.size() + " sets told apart");
        CodePoints all = CodePoints.NONE;
        for (CodePoints each : alike) {
            assertTrue(all.and(each).isEmpty(), "two of them hold a code point in common");
            all = all.or(each);
        }
        assertEquals(CodePoints.EVERYTHING, all, "together they hold every code point");
    }
}
