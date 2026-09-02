package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.ast.Ast;
import souther.compiler.ast.Hir;
import souther.compiler.check.Resolve;
import souther.compiler.check.SyntaxSymbols;
import souther.compiler.check.Symbols;
import souther.compiler.frontend.CstFrontend;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.Position;
import souther.compiler.inputs.TermPath;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;
import souther.compiler.types.TypeSymbol;

import java.util.List;


import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What one reading of a position comes to, and which of its answers an absence may be built on.
 *
 * <p>{@code Open} is a sentence about the model: its local rules were read to the end and it states
 * no division here. Written instead as "the producers came back empty", the sentence was a tally,
 * and a producer added later stayed outside what "everything was asked" meant — which is how a
 * position whose invariant names the two values it may hold was reported as one the model divides
 * no way (issue #772).
 *
 * <p>So the three answers are held from the outside: what each of them claims, and the two ways of
 * writing one that claims more than the reading found. {@code Open} carries no account of the
 * reading, which is what makes a reading short of the rules unable to be written as one.
 *
 * <p>Over the positions the language can currently be in, which is the whole claim. A position
 * carrying both a division and children would say something further about the precedence, and no
 * model can be written that has one — only products have children, and a product carries neither
 * classes nor cuts. Building one out of a hand-made {@code Shape} would fix the implementation's
 * product space rather than the language's, so the rows here are the reachable ones.
 */
class AnOpenPositionIsAReadingThatRanToTheEndTest {

    private static final String MODULE = """
            module demo

            data Prospecting
            data Qualified
            data Won
            data Stage = Prospecting | Qualified | Won

            data Amount = Int invariant value >= 100
            data Plain = Int
            data Slot = { hour: Int, room: String }
            data Gender = String invariant value == "A" || value == "B"
            data Email = String invariant UNREAD
            """.replace("UNREAD", souther.compiler.ARuleNoReadingTakesIn.about("value"));

    private final Symbols symbols = Symbols.of(resolved(), DefaultStdlib.get());

    private static Hir.Module resolved() {
        Ast.Module parsed = CstFrontend.parse(MODULE);
        return Resolve.module(parsed, SyntaxSymbols.of(parsed, DefaultStdlib.get()));
    }

    private TypeSymbol named(String type) {
        return TypeSymbols.declared(new TypeKey(symbols.module(), type));
    }

    /** As a parameter is read: under the declaration the signature wrote, with what is written
     *  about it. */
    private Position read(String type) {
        return InputDomain.of(
                        List.of(new InputDomain.Parameter("x", null, Type.ref(named(type)))),
                        symbols, souther.compiler.query.ReadAs.THE_COMPILATION_DOES)
                .at(TermPath.of("x"));
    }

    /** What the reading of {@code type} came to. */
    private LocalPartition partitionOf(String type) {
        return LocalInspection.of(read(type), symbols, souther.compiler.query.ReadAs.THE_COMPILATION_DOES);
    }

    /** A type that states cases divides the position, and no line is drawn through them. */
    @Test
    void classesAndNoLineIsADivision() {
        LocalPartition.Divided found =
                assertInstanceOf(LocalPartition.Divided.class, partitionOf("Stage"));

        assertEquals(List.of("Prospecting", "Qualified", "Won"),
                found.classes().stream().map(PartitionClass::id).toList());
        assertInstanceOf(CutEvidence.None.class, found.cuts());
    }

    /** A rule that says where the values stop divides it too, and puts no class either side of the
     *  line — everything outside it is refused at construction. */
    @Test
    void aLineAndNoClassIsADivisionToo() {
        LocalPartition.Divided found =
                assertInstanceOf(LocalPartition.Divided.class, partitionOf("Amount"));

        assertEquals(List.of(), found.classes());
        assertInstanceOf(CutEvidence.Present.class, found.cuts());
        assertTrue(found.cuts().cuts().size() >= 1);
    }

    /** And a rule that names the values it may hold divides it into those, which is the third way
     *  and was read by nothing. */
    @Test
    void theValuesARuleNamesAreADivisionAsWell() {
        LocalPartition.Divided found =
                assertInstanceOf(LocalPartition.Divided.class, partitionOf("Gender"));

        assertEquals(2, found.classes().size(), found.classes().toString());
    }

    /** Nothing written about the position, read to the end: the model divides it no way, and that
     *  is what licenses asking what is under it. */
    @Test
    void nothingWrittenAndReadToTheEndIsOpen() {
        assertInstanceOf(LocalPartition.Open.class, partitionOf("Plain"));
        assertInstanceOf(LocalPartition.Open.class, partitionOf("Slot"));
    }

    /**
     * A rule written here that nothing could read is open as well, and the position is not an
     * absence.
     *
     * <p>What this reading found is that nothing it read divides the position, which is the same
     * answer it gives where nothing is written at all. What keeps the absence above from being
     * claimed here is not held by this reading: the rule raises a question, and no reading answered
     * it, so the position is one nothing about the model follows from. Answered here instead, a
     * reading short of a rule that another reading took in wrote the position down as one this
     * compiler could not read.
     */
    @Test
    void aRuleNothingCouldReadLeavesAQuestionRatherThanAnAnswerHere() {
        assertInstanceOf(LocalPartition.Open.class, partitionOf("Email"));

        assertEquals(1, read("Email").unansweredQuestions().size(),
                "the rule nothing read raises a question, and nothing answered it");
        assertEquals(List.of(), read("Gender").unansweredQuestions(),
                "and a rule a reading took in raises none that stands");
    }

    /** The reading is there whichever answer it is: what the position is measured at, and what its
     *  rules leave its values, are not things only a divided position has. */
    @Test
    void theReadingIsTheSameValueWhicheverAnswerItIs() {
        for (String type : List.of("Stage", "Amount", "Plain", "Slot", "Gender", "Email")) {
            Position position = read(type);
            assertNotNull(position.term(), type + " is measured at some term");
            assertNotNull(position.reading(), type + " says which values it may hold");
            assertNotNull(position.completeness(), type + " says how much of its rules was read");
            assertNotNull(position.rulesWithoutALine(), type + " says which of its rules went unread");
        }
    }

    /** An answer that says nothing cannot be written as one that says something. */
    @Test
    void anEmptyDivisionIsNotAnAnswer() {
        assertThrows(IllegalArgumentException.class,
                () -> new LocalPartition.Divided(List.of(), new CutEvidence.None()));
    }

    /**
     * There is no way to make one of these except by deriving it.
     *
     * <p>What holds the sentence up. A conclusion its reading does not support — an open position
     * off a reading short of the rules, classes said to be read in full off one that was not — is
     * not refused when somebody writes it; there is nowhere to write it. Both halves are asserted,
     * because the discipline is now split across them: the reading is a value nothing outside the
     * package that makes it can construct, and the conclusion has one derivation and no other way
     * in. Held here because it is a property of the boundary rather than of any one value: a
     * constructor added later would put back the discipline this replaced, and nothing else in the
     * suite would notice.
     */
    @Test
    void nothingButTheDerivationMakesOne() {
        assertEquals(List.of(), java.util.Arrays.stream(LocalInspection.class.getConstructors())
                .map(java.lang.reflect.Constructor::toString).toList(),
                "a conclusion anybody can make is one anybody can make disagree with its reading");
        assertEquals(List.of("of"),
                java.util.Arrays.stream(LocalInspection.class.getDeclaredMethods())
                        .filter(each -> !java.lang.reflect.Modifier
                                .isPrivate(each.getModifiers()))
                        .map(java.lang.reflect.Method::getName).sorted().toList(),
                "one derivation, and it is the one that reads the position");
        assertTrue(Position.class.isSealed(),
                "a reading anybody can implement is one anybody can answer with");
        for (Class<?> each : Position.class.getPermittedSubclasses()) {
            assertEquals(0, each.getConstructors().length,
                    each.getSimpleName() + " can be written down outside the reading that makes it");
        }
    }

    /** And neither can no lines at all be written as lines. */
    @Test
    void noCutsIsNotAPresentCut() {
        assertThrows(IllegalArgumentException.class,
                () -> new CutEvidence.Present(List.of(),
                        new souther.compiler.check.ProjectionEvidence.CertifiedExact(
                                new souther.compiler.numeric.ProjectionCertificate
                                        .ByBoxAndClosedDifferences())));
    }
}
