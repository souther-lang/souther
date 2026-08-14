package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Ast;
import souther.compiler.ast.Hir;
import souther.compiler.check.Resolve;
import souther.compiler.check.SyntaxSymbols;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeView;
import souther.compiler.frontend.CstFrontend;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;
import souther.compiler.types.TypeName;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a position's own type and rules say is one answer, and it comes from asking both producers.
 *
 * <p>The classes a type states and the lines its rules draw were two lists, and "local evidence has
 * run out" was a caller noticing that both were empty. Anything that read one of them and went on
 * would have concluded it from half the evidence — and what follows from that conclusion is the
 * whole rest of the derivation, since only an exhausted local reading licenses asking what is under
 * the position.
 *
 * <p>So {@code Exhausted} is a value nothing but the reading can produce, and {@code Evidence}
 * cannot be built empty. These hold that from the outside: the three shapes of local answer, and
 * the two ways of writing one that says nothing while claiming to say something.
 *
 * <p>Over the positions the language can currently be in, which is the whole claim. A position
 * carrying both local evidence and children would say something further about the precedence, and
 * no model can be written that has one — only products have children, and a product carries neither
 * classes nor cuts. Building one out of a hand-made {@code Shape} would fix the implementation's
 * product space rather than the language's, so the rows here are the reachable ones.
 */
class LocalEvidenceIsAskedOfBothProducersTest {

    private static final String MODULE = """
            module demo

            data Prospecting
            data Qualified
            data Won
            data Stage = Prospecting | Qualified | Won

            data Amount = Int invariant value >= 100
            data Plain = Int
            data Slot = { hour: Int, room: String }
            """;

    private final Symbols symbols = Symbols.of(resolved());

    private static Hir.Module resolved() {
        Ast.Module parsed = CstFrontend.parse(MODULE);
        return Resolve.module(parsed, SyntaxSymbols.of(parsed));
    }

    private LocalInspection inspect(String type) {
        return LocalInspection.inspect(
                PartitionInput.of(TypeView.of(Type.ref(TypeSymbols.declared(new TypeKey(symbols.module(), type))), symbols)),
                TermPath.of("x"), symbols, null);
    }

    /** A type that states cases: evidence, and no line drawn through them. */
    @Test
    void classesAndNoLineIsEvidence() {
        LocalInspection.Evidence found =
                assertInstanceOf(LocalInspection.Evidence.class, inspect("Stage"));

        assertEquals(List.of("Prospecting", "Qualified", "Won"),
                found.classes().stream().map(PartitionClass::id).toList());
        assertInstanceOf(CutEvidence.None.class, found.cuts());
    }

    /** A rule that says where the values stop: evidence, and no class either side of the line —
     *  everything outside it is refused at construction. */
    @Test
    void aLineAndNoClassIsEvidenceToo() {
        LocalInspection.Evidence found =
                assertInstanceOf(LocalInspection.Evidence.class, inspect("Amount"));

        assertEquals(List.of(), found.classes());
        assertInstanceOf(CutEvidence.Present.class, found.cuts());
        assertTrue(found.cuts().cuts().size() >= 1);
    }

    /** Neither producer had anything, which is the answer that licenses asking what is under the
     *  position — and is not the same as either of them being empty. */
    @Test
    void neitherIsExhausted() {
        assertInstanceOf(LocalInspection.Exhausted.class, inspect("Plain"));
        assertInstanceOf(LocalInspection.Exhausted.class, inspect("Slot"));
    }

    /** The reading is there either way: what the position is measured at is not a thing only a
     *  position with evidence has. */
    @Test
    void theReadingIsTheSameValueWhicheverAnswerItIs() {
        for (String type : List.of("Stage", "Amount", "Plain", "Slot")) {
            LocalReading reading = inspect(type).reading();
            assertNotNull(reading.term(), type + " is measured at some term");
            assertNotNull(reading.unread(), type + " says which of its rules went unread");
        }
    }

    /** An answer that says nothing cannot be written as one that says something. */
    @Test
    void anEmptyEvidenceIsNotAnAnswer() {
        LocalReading reading = inspect("Plain").reading();

        assertThrows(IllegalArgumentException.class,
                () -> new LocalInspection.Evidence(reading, List.of(), new CutEvidence.None()));
    }

    /** And neither can no lines at all be written as lines. */
    @Test
    void noCutsIsNotAPresentCut() {
        assertThrows(IllegalArgumentException.class,
                () -> new CutEvidence.Present(List.of(), false));
    }
}
