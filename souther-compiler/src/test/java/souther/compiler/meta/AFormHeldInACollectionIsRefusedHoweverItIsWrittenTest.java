package souther.compiler.meta;

import souther.compiler.ast.Hir;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.Type;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A form of a declaration held in a set, or used as a map key, stops the comparison — whether it is
 * written as a record or by hand.
 *
 * <p>A set compares what it holds by that thing's own equality, and a form's own equality reads
 * where it was written and which binding it is: the two things a crossing cannot see and this
 * comparison erases. So a form arriving in one is compared by a rule the comparison does not
 * control, and it says so rather than answering.
 *
 * <p>Asked of the refusal itself because nothing reaches it. Neither build puts a form in a set
 * today, so there is no pair of declarations that would make the walk arrive at one — and a refusal
 * nothing reaches is one that can stop covering a case without anything failing. That is not
 * hypothetical here: the reading of forms one door along went on passing while the set it read over
 * got smaller, for want of exactly this.
 */
class AFormHeldInACollectionIsRefusedHoweverItIsWrittenTest {

    private static final SourcePos POS = new SourcePos(1, 1);

    /** A form written by hand rather than as a record. */
    private static Hir.RetType aWrittenType() {
        return Hir.RetType.of(List.of(Hir.TypeRef.of(Type.BOOL, POS)), POS);
    }

    @Test
    void aFormWrittenAsARecordIsRefused() {
        assertThrows(IllegalStateException.class,
                () -> DeclarationAgreement.refuseForms(Set.of(Hir.TypeRef.of(Type.BOOL, POS))),
                "a reference is a form, and a set of them compares them by what they carry");
    }

    @Test
    void andSoIsOneWrittenByHand() {
        assertThrows(IllegalStateException.class,
                () -> DeclarationAgreement.refuseForms(Set.of(aWrittenType())),
                "a written type is a form however it is written, and a set of them would compare"
                        + " them by an equality that reads where they stand");
    }

    /**
     * The control: something a set may hold goes through.
     *
     * <p>Without it a refusal that took everything would pass both of the above by taking
     * everything, and the two would say nothing about which things it is for.
     */
    @Test
    void andSomethingThatIsNoFormGoesThrough() {
        assertDoesNotThrow(() -> DeclarationAgreement.refuseForms(Set.of("a word")),
                "a word is compared by being that word, whoever holds it");
    }
}
