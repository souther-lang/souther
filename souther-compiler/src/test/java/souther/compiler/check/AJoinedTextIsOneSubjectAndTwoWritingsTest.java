package souther.compiler.check;

import souther.compiler.DefaultStdlib;
import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.query.ReadAs;
import souther.compiler.types.BinOp;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.Type;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * Two texts joined are the text they come to as a subject, and still the two that were joined as a
 * shape.
 *
 * <p>Two readings of one walk, asked two questions. Which value a fact is about is answered by what
 * the value is, so {@code "J" ++ "P"} and {@code "JP"} are one subject. Whether the reading can say
 * what an expression is written as is answered by the writing, so they are two keys there, as they
 * were. Only a text: a sum of numbers is filed as the sum it was written as, whatever it comes to.
 */
class AJoinedTextIsOneSubjectAndTwoWritingsTest {

    private static final SourcePos POS = new SourcePos(1, 1);
    private static final BindingOwner OWNER = new BindingOwner.OfValue("demo", "f");

    private static Terms terms() {
        return RuleReadings.termsOfNoClauseFiled(Symbols.none(DefaultStdlib.get()),
                ReadAs.THE_COMPILATION_DOES);
    }

    private static Core text(String value) {
        return new Core.Str(value, Type.STRING, POS);
    }

    private static Core joined(Core left, Core right) {
        return new Core.Binary(BinOp.CONCAT, left, right, Core.BinaryReading.AS_THEY_STAND,
                ConstructOccurrence.unwritten(), Type.STRING, POS);
    }

    private static Core sum(long left, long right) {
        return new Core.Binary(BinOp.ADD, new Core.Int(left, Type.INT, POS),
                new Core.Int(right, Type.INT, POS), Core.BinaryReading.AS_THEY_STAND,
                ConstructOccurrence.unwritten(), Type.INT, POS);
    }

    /** {@code p}, an input standing at a place of its own. */
    private static Core.Read input(String name, int index, Denotations[] at) {
        BindingId binding = new BindingId(OWNER, index);
        at[0] = at[0].location(binding, AsPlaces.of(binding), AsPlaces.term(binding));
        return new Core.Read(name, binding, Type.STRING, POS);
    }

    @Test
    void asASubjectTheyAreOneText() {
        Terms terms = terms();
        Denotations at = Denotations.none();
        assertEquals(terms.subjectOf(text("JP"), at),
                terms.subjectOf(joined(text("J"), text("P")), at));
        assertEquals(terms.subjectOf(text("JPN"), at),
                terms.subjectOf(joined(joined(text("J"), text("P")), text("N")), at),
                "a text joined to a joined text");
    }

    @Test
    void asAWritingTheyAreTwo() {
        Terms terms = terms();
        Denotations at = Denotations.none();
        Term literal = terms.bodyKey(text("JP"), at);
        Term written = terms.bodyKey(joined(text("J"), text("P")), at);
        assertNotNull(written, "the symbolic reading still reads a join it is written as");
        assertNotEquals(literal, written);
    }

    @Test
    void aTextJoinedToAnInputIsNoTextAndNotAnotherInputs() {
        Terms terms = terms();
        Denotations[] at = {Denotations.none()};
        Core p = input("p", 0, at);
        Core q = input("q", 1, at);
        FactSubject overP = terms.subjectOf(joined(text("J"), p), at[0]);
        assertNotEquals(terms.subjectOf(text("J"), at[0]), overP);
        assertNotEquals(terms.subjectOf(joined(text("J"), q), at[0]), overP);
    }

    @Test
    void aSumIsNotTheNumberItComesTo() {
        Terms terms = terms();
        Denotations at = Denotations.none();
        assertNotEquals(terms.subjectOf(new Core.Int(2, Type.INT, POS), at),
                terms.subjectOf(sum(1, 1), at));
    }
}
