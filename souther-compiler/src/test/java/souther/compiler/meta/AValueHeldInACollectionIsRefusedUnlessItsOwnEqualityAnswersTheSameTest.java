package souther.compiler.meta;

import souther.compiler.ast.Hir;
import souther.compiler.ast.WrittenName;
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

    /** A form written to hold anything, which is what its part says about what it holds. */
    private record Holds<T>(T value) {}

    /**
     * A value the walk does not take apart is handed to its own equality, so a set of them is held
     * the way this comparison holds them.
     *
     * <p>Where the walk stops, {@code ConstEval.equal} answers, and that is the value's own
     * equality. What such a value keeps inside is read by that equality on both sides — by the
     * collection and by this comparison alike — so keeping something this would have read its own
     * way is not a reason to refuse one. An expansion keeps a name the comparison would have held
     * by what it stands for, and it is still held the same either way, because neither side ever
     * looks.
     */
    @Test
    void aValueTheWalkDoesNotTakeApartIsHeldByTheEqualityBothSidesUse() {
        ValueName.Local aBinding =
                new ValueName.Local("n", new BindingId(new BindingOwner.OfValue("demo", "f"), 0));

        assertFalse(StructuralParts.areHandedOver(KeepsABinding.class),
                "the walk stops at it, which is what hands it to its own equality");
        assertThrows(IllegalStateException.class,
                () -> DeclarationAgreement.refuseWhatThisComparisonAnswersDifferently(
                        Set.of(aBinding)),
                "the binding it keeps is one this comparison holds by what it stands for");

        assertDoesNotThrow(
                () -> DeclarationAgreement.refuseWhatThisComparisonAnswersDifferently(
                        Set.of(new KeepsABinding(aBinding))),
                "and keeping one is still held the same either way, because neither side looks");

        assertFalse(StructuralParts.areHandedOver(BindingOwner.Expansion.class),
                "an expansion is such a value, which is why keeping a name inside one is no reason"
                        + " to refuse it");
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
