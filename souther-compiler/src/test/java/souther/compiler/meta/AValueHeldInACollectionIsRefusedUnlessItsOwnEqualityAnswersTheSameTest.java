package souther.compiler.meta;

import souther.compiler.ast.Hir;
import souther.compiler.ast.WrittenName;
import souther.compiler.crossing.ObjectEqualityIsTheCrossingAnswer;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.util.ArrayDeque;
import java.util.Deque;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A set compares what it holds by that thing's own equality, and a map its keys. What may be held
 * in one is what this comparison would have answered the same about, and nothing else.
 *
 * <p>Two questions used to be one here. Whether a value's parts can be read is about how the value
 * is written; whether its own equality is this comparison is about what this comparison does. They
 * are independent, and asking the first in place of the second answered by how a value happened to
 * be written: a settled name written as a record was refused and the same name written as a class
 * went through, while a binding — which this comparison holds by what it stands for and never by
 * which one it is — went through because it is written as a class.
 *
 * <p>So what is held here is the second question, over values on both sides of it. Asked of the
 * refusal itself because nothing reaches it: neither build puts such a value in a set today, so
 * there is no pair of declarations that would make the walk arrive at one — and a refusal nothing
 * reaches is one that can stop covering a case without anything failing. That is not hypothetical
 * here: the reading of forms one door along went on passing while the set it read over got smaller,
 * for want of exactly this.
 */
class AValueHeldInACollectionIsRefusedUnlessItsOwnEqualityAnswersTheSameTest {

    private static final SourcePos POS = new SourcePos(1, 1);

    /**
     * A settled name goes through, whichever of its arms it is.
     *
     * <p>One arm is written as a record and one as a class, and that is the difference the old
     * question answered by. Both are here for that: what a set may hold cannot depend on it.
     */
    @Test
    void aSettledNameIsHeldByItsOwnEqualityWhicheverArmItIs() {
        TypeSymbol written = TypeSymbols.declared(new TypeKey("demo", "Amount"));
        TypeSymbol ofTheLanguage = new TypeSymbol.Primitive(Type.Prim.INT);

        assertFalse(written.getClass().isRecord(),
                "the arm standing for a declaration is written as a class");
        assertTrue(ofTheLanguage.getClass().isRecord(),
                "and the one standing for a primitive as a record");

        assertDoesNotThrow(
                () -> DeclarationAgreement.refuseWhatThisComparisonAnswersDifferently(
                        Set.of(written, ofTheLanguage)),
                "what a settled name is, is what this comparison reads it by, so a set holding one"
                        + " settles nothing this does not");
    }

    /**
     * A value read here by the answer settled beside its spelling is refused, the spelling being
     * something its own equality reads and this passes over.
     *
     * <p>A type used as a value carries the word it was reached by and the declaration that word
     * reaches. Nothing of it is erased and nothing of it is a binding — it is the answer standing in
     * for a spelling and nothing else, which is why it is the one asked here. Two builds that wrote
     * one type under two names are one to this comparison and two to an equality of these, so a set
     * of them would hold apart what this holds together.
     */
    @Test
    void aValueReadByTheAnswerSettledBesideItsSpellingIsRefused() {
        ValueName.OfType usedAsAValue = new ValueName.OfType(
                "Amount", TypeSymbols.declared(new TypeKey("demo", "Amount")));

        assertFalse(DeclarationAgreement.erases(ValueName.OfType.class),
                "nothing of it is passed over, so erasure is not what refuses it");
        assertTrue(DeclarationAgreement.readByTheAnswerBesideItsSpelling(ValueName.OfType.class),
                "what refuses it is the arm the comparison reads it by");
        assertThrows(IllegalStateException.class,
                () -> DeclarationAgreement.refuseWhatThisComparisonAnswersDifferently(
                        Set.of(usedAsAValue)),
                "this reads the type it was settled to be and passes the word over, which an"
                        + " equality of it does not");
    }

    /** A form of the grammar reaches where it was written, which this passes over. */
    @Test
    void aFormThatReachesWhereItWasWrittenIsRefused() {
        assertThrows(IllegalStateException.class,
                () -> DeclarationAgreement.refuseWhatThisComparisonAnswersDifferently(
                        Set.of(Hir.TypeRef.of(Type.BOOL, POS))),
                "a reference holds where it stands, and an equality of it reads that");
    }

    /** And one written by hand rather than as a record is the same value to this, the writing being
     *  no part of the question. */
    @Test
    void andSoIsOneWrittenByHand() {
        Hir.RetType writtenType = Hir.RetType.of(List.of(Hir.TypeRef.of(Type.BOOL, POS)), POS);

        assertThrows(IllegalStateException.class,
                () -> DeclarationAgreement.refuseWhatThisComparisonAnswersDifferently(
                        Set.of(writtenType)),
                "a written type reaches where it is written, which this passes over and an equality"
                        + " of it reads");
    }

    /**
     * A binding is refused, which the question this used to ask let through.
     *
     * <p>This comparison holds two bindings by what they stand for across the two builds and never
     * by which one each is, so a set of them is the plainest case there is of a collection settling
     * what this class was written to settle. It went through because a binding is written as a
     * class rather than as a record, which is not a fact about bindings.
     */
    @Test
    void aBindingIsRefusedBecauseThisComparisonHoldsItByWhatItStandsFor() {
        BindingId binding = new BindingId(new BindingOwner.OfValue("demo", "f"), 0);

        assertFalse(binding.getClass().isRecord(),
                "a binding is written as a class, which is what let it through");
        assertThrows(IllegalStateException.class,
                () -> DeclarationAgreement.refuseWhatThisComparisonAnswersDifferently(
                        Set.of(binding)),
                "two bindings are held here by standing for each other, which nothing a set does"
                        + " can arrive at");
    }

    /**
     * A written number is refused, this comparison holding two of them by what they count.
     *
     * <p>{@code 1.0m} and {@code 1.00m} are one number wherever else two of them meet, and this says
     * so; an equality of them reads how many places each was written to. A set of them would report
     * a build as moved over a difference the model does not have.
     */
    @Test
    void aWrittenNumberIsRefusedBecauseThisComparisonHoldsItByWhatItCounts() {
        assertEquals(0, new BigDecimal("1.0").compareTo(new BigDecimal("1.00")),
                "one number, which is what this comparison holds two of them by");
        assertNotEquals(new BigDecimal("1.0"), new BigDecimal("1.00"),
                "and two values, which is what an equality of them reads");

        assertThrows(IllegalStateException.class,
                () -> DeclarationAgreement.refuseWhatThisComparisonAnswersDifferently(
                        Set.of(new BigDecimal("1.0"))),
                "so a set of them holds apart what this holds together");
    }

    /**
     * The control: something a collection may hold goes through.
     *
     * <p>Without it a refusal that took everything would pass every case above by taking
     * everything, and none of them would say which values it is for.
     */
    @Test
    void andAWrittenWordGoesThrough() {
        assertDoesNotThrow(
                () -> DeclarationAgreement.refuseWhatThisComparisonAnswersDifferently(
                        Set.of("a word")),
                "a word is compared by being that word, whoever holds it");
    }

    /**
     * A container is read through, so it answers whatever what it holds answers.
     *
     * <p>Not a value of its own. The comparison unwraps an optional and walks a list, so two of
     * either are one wherever what they hold is one — and a collection asked the same question
     * calls the equality of what they hold. So the question passes through, and asking it of the
     * container as a kind would answer for every element it might ever hold at once.
     */
    @Test
    void aContainerAnswersWhateverWhatItHoldsAnswers() {
        ValueName.Local aBinding =
                new ValueName.Local("n", new BindingId(new BindingOwner.OfValue("demo", "f"), 0));

        assertThrows(IllegalStateException.class,
                () -> DeclarationAgreement.refuseWhatThisComparisonAnswersDifferently(
                        Set.of(Optional.of(aBinding))),
                "an optional of a binding is a binding as far as this reads it");
        assertThrows(IllegalStateException.class,
                () -> DeclarationAgreement.refuseWhatThisComparisonAnswersDifferently(
                        Set.of(List.of(aBinding))),
                "and so is a list of them");

        assertDoesNotThrow(
                () -> DeclarationAgreement.refuseWhatThisComparisonAnswersDifferently(
                        Set.of(Optional.of("a word"), List.of("a word"))),
                "while a container of words holds what a collection may hold, which is why this is"
                        + " asked of what is in hand and not of the container");
    }

    /**
     * And a container the comparison has no arm for is not read through, holding a binding or not.
     *
     * <p>The walk stopping at it is not a reason it may be held. That was the reason once: what the
     * walk does not take apart goes to its own equality, so both sides ask the same thing and a set
     * reaches the same answer. It holds for whatever the walk stops at, including this — a queue
     * answers the equality every object is given, which is whether it is the same queue, and two
     * builds each holding their own would never be one whatever they held.
     */
    @Test
    void andAContainerWithNoArmIsRefusedLikeAnythingElseNobodySpeaksFor() {
        Deque<ValueName.Local> queued = new ArrayDeque<>();
        queued.add(new ValueName.Local("n", new BindingId(new BindingOwner.OfValue("demo", "f"), 0)));

        assertFalse(StructuralParts.areHandedOver(queued.getClass()),
                "the walk stops at it, which used to be the whole of why a set could hold one");
        assertThrows(IllegalStateException.class,
                () -> DeclarationAgreement.refuseWhatThisComparisonAnswersDifferently(
                        Set.of(queued)),
                "and nobody has said what a set makes of one answers what this comparison would");
    }

    /**
     * What a value holds is read off the value, so a part whose type says nothing is no gap.
     *
     * <p>A form written to hold anything says only that, and a reading that answered off the
     * declared part would have nothing there to be refused by — it would call every one of them
     * safe. What arrives is what this comparison will meet, and that is what is asked.
     */
    @Test
    void andWhatAPartSaysNothingAboutIsStillAskedOfWhatArrived() {
        ValueName.Local aBinding =
                new ValueName.Local("n", new BindingId(new BindingOwner.OfValue("demo", "f"), 0));

        assertDoesNotThrow(
                () -> DeclarationAgreement.refuseWhatThisComparisonAnswersDifferently(
                        Set.of(new Holds<>("a word"))),
                "one holding a word holds what a collection may hold");
        assertThrows(IllegalStateException.class,
                () -> DeclarationAgreement.refuseWhatThisComparisonAnswersDifferently(
                        Set.of(new Holds<>(aBinding))),
                "and one holding a binding is refused, though the two are one type");
    }

    /** A form written to hold anything, which is what its part says about what it holds. It says a
     *  collection may hold it, which is a claim about its own equality and none about what
     *  arrives. */
    private record Holds<T>(T value) implements ObjectEqualityIsTheCrossingAnswer {}

    /**
     * A value the walk does not take apart is refused until somebody says a collection may hold it.
     *
     * <p>This is where the reading used to answer from the walk. A value the walk stops at goes to
     * its own equality, and that was read as: both sides ask that equality, so a set reaches what
     * this comparison reaches. The trouble is that it holds for every value the walk stops at,
     * including one whose equality reads what this comparison cannot see — so the reading could not
     * come out false for exactly the values whose holding rested on it.
     *
     * <p>The one below is that value. It keeps a use of a binding and its equality reads it, which
     * is the spelling as well as the binding; this comparison holds two uses by what they stand
     * for and never by the word. Two builds that renamed a local would be two here and one there,
     * and the old reading called it safe.
     */
    @Test
    void aValueTheWalkDoesNotTakeApartIsRefusedUntilSomebodySpeaksForIt() {
        ValueName.Local aBinding =
                new ValueName.Local("n", new BindingId(new BindingOwner.OfValue("demo", "f"), 0));

        assertFalse(StructuralParts.areHandedOver(KeepsABinding.class),
                "the walk stops at it, which used to be the whole of why a set could hold one");
        assertThrows(IllegalStateException.class,
                () -> DeclarationAgreement.refuseWhatThisComparisonAnswersDifferently(
                        Set.of(aBinding)),
                "the binding it keeps is one this comparison holds by what it stands for");

        assertThrows(IllegalStateException.class,
                () -> DeclarationAgreement.refuseWhatThisComparisonAnswersDifferently(
                        Set.of(new KeepsABinding(aBinding))),
                "and keeping one inside is not made safe by the walk stopping outside it");
    }

    /**
     * A form whose parts a reader can go inside is refused all the same, its parts being no account
     * of what its equality reads.
     *
     * <p>The two questions that used to be one. What a reader can take a form apart into is what a
     * comparison of two builds reads of it; what a set makes of the form is what its equality
     * reads. A form written by hand can be walked into and compare by whatever its writer chose —
     * the one below reads the word it holds, and could as easily read where the word was written —
     * so parts that a collection may hold are no reason the form is one.
     *
     * <p>Which is what the whole of this is about, one question over. The reading that decides
     * these used to take the walk's answer for the equality's; taking the parts' answer for the
     * form's is the same purchase from the same wrong place.
     */
    @Test
    void andAFormAReaderCanGoInsideIsStillRefusedForWhatNobodySaidAboutItsEquality() {
        assertTrue(StructuralParts.areHandedOver(KeepsAWord.class),
                "a reader goes inside it, and every part it finds is one a collection may hold");
        assertDoesNotThrow(
                () -> DeclarationAgreement.refuseWhatThisComparisonAnswersDifferently(
                        Set.of("a word")),
                "the part being that word, which a set may hold");

        assertThrows(IllegalStateException.class,
                () -> DeclarationAgreement.refuseWhatThisComparisonAnswersDifferently(
                        Set.of(new KeepsAWord("a word"))),
                "and the form is refused all the same, because what its equality reads is not what"
                        + " a reader going inside it finds");
    }

    /** A form of the grammar written by hand, holding what a collection may hold. Its equality
     *  reads the word; nothing here says so, which is the point. */
    private static final class KeepsAWord implements Hir.Shape {

        private final String word;

        private KeepsAWord(String word) {
            this.word = word;
        }

        public String word() {
            return word;
        }

        @Override
        public boolean equals(Object other) {
            return other instanceof KeepsAWord kept && word.equals(kept.word);
        }

        @Override
        public int hashCode() {
            return word.hashCode();
        }
    }

    /**
     * The control: a value the walk does not take apart goes through once somebody has said so.
     *
     * <p>Without it the refusal would be taking every such value rather than the ones nobody has
     * spoken for, and the case above would not be about what it says it is about.
     */
    @Test
    void andOneSomebodyHasSpokenForGoesThrough() {
        assertFalse(StructuralParts.areHandedOver(TypeSymbol.AtModule.class),
                "the walk stops at it, as it stops at the one refused above");
        assertDoesNotThrow(
                () -> DeclarationAgreement.refuseWhatThisComparisonAnswersDifferently(
                        Set.of(TypeSymbols.declared(new TypeKey("demo", "Amount")))),
                "and it names the address its equality is over, which is a pair of words this"
                        + " comparison reads as the words they are");
    }

    /** Stands for a value the walk stops at, keeping something it would have read its own way. */
    private static final class KeepsABinding {

        private final ValueName.Local binding;

        private KeepsABinding(ValueName.Local binding) {
            this.binding = binding;
        }

        @Override
        public boolean equals(Object other) {
            return other instanceof KeepsABinding kept && binding.equals(kept.binding);
        }

        @Override
        public int hashCode() {
            return binding.hashCode();
        }
    }

    /** A map's keys are asked the same question, a key being held by its own equality the way a
     *  set's element is. */
    @Test
    void aMapIsAskedOfItsKeysTheSameWay() {
        Map<Hir.TypeRef, String> keyed = Map.of(Hir.TypeRef.of(Type.BOOL, POS), "a value");

        assertThrows(IllegalStateException.class,
                () -> DeclarationAgreement.refuseWhatThisComparisonAnswersDifferently(
                        keyed.keySet()),
                "a key is held by its own equality, so what may be one is what may be held");
    }

    /**
     * A value is refused for what its parts reach, and not only for what it is.
     *
     * <p>The witness for that, and the reason it is a written name. A name is none of the things
     * this comparison answers differently about: it is not passed over, since which of them a value
     * is read under is that word, and nothing stands beside the word to be read in its place. What
     * refuses it is a part of it — where each piece of the word was written, which this erases and
     * an equality of it reads. So a reading that answered off the value in hand would call a set of
     * names safe to hold, and it would hold apart two builds that wrote one name in two places.
     *
     * <p>The two assertions below are what say so: they rule out each way the value itself could
     * have been the reason, leaving the part it reaches as the only one left.
     */
    @Test
    void aValueIsRefusedForWhatItsPartsReachAndNotOnlyForWhatItIs() {
        WrittenName aWord = new WrittenName("amount", null, List.of(), POS);

        assertFalse(DeclarationAgreement.erases(WrittenName.class),
                "a name is not passed over — which of them a value is read under is that word");
        assertFalse(DeclarationAgreement.readByTheAnswerBesideItsSpelling(WrittenName.class),
                "and nothing stands beside the word to be read in its place");

        assertThrows(IllegalStateException.class,
                () -> DeclarationAgreement.refuseWhatThisComparisonAnswersDifferently(
                        Set.of(aWord)),
                "so what refuses it is what it holds: where the word was written, which this erases"
                        + " and an equality of it reads");
    }
}
