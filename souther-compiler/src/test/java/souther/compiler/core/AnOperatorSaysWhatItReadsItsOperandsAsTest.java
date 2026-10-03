package souther.compiler.core;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.types.BinOp;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.Type;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * What an operator reads its operands as is in the tree, where the checker settled it, and is not a
 * function of the three types a reader can see.
 *
 * <p>{@code i + j} and {@code i / j} both read two {@code Int}s as they stand, and only the answer
 * differs. {@code i + r} reads the {@code Int} at its exact value, which is no type either operand
 * has. {@code a <= 100} reads the literal as the newtype beside it, and the literal is still an
 * {@code Int}. Newtype arithmetic says nothing of its own: the tree already holds it as the
 * operation over what the newtypes wrap.
 */
class AnOperatorSaysWhatItReadsItsOperandsAsTest {

    private static final String MODULE = """
            module demo

            data Amount = Int

            data Prospecting
            data Qualified
            data Won
            data Stage = Prospecting | Qualified | Won

            data Circle = { r: Int }
            data Square = { side: Int }
            data Shape  = Circle | Square

            behavior whole : (i: Int, j: Int) -> Int
            let whole (i, j) = i + j

            behavior quotient : (i: Int, j: Int) -> Bool
            let quotient (i, j) = i / j > 1

            behavior exactSum : (i: Int, j: Int) -> Bool
            let exactSum (i, j) = i + j / 2 > 1

            behavior exactlyEqual : (d: Decimal, j: Int) -> Bool
            let exactlyEqual (d, j) = d == j / 2

            behavior underALimit : (a: Amount) -> Bool
            let underALimit (a) = a <= 100

            behavior beforeWon : (s: Stage) -> Bool
            let beforeWon (s) = s < Won

            behavior aCircle : (s: Shape) -> Bool
            let aCircle (s) = s == Circle { r = 1 }

            behavior appended : (n: Int) -> List<Shape>
            let appended (n) = [Circle { r = n }] ++ [Square { side = n }]

            behavior doubled : (a: Amount) -> Amount
            let doubled (a) = a + a

            data StageN = Stage

            behavior aCaseAgainstItself : (w: Won) -> Bool
            let aCaseAgainstItself (w) = w <= w

            behavior casesOfOneSum : (f: Bool) -> Bool
            let casesOfOneSum (f) =
                (if f then Won else Qualified) < (if f then Qualified else Won)

            behavior aSumAgainstItself : (s: Stage, t: Stage) -> Bool
            let aSumAgainstItself (s, t) = s < t

            behavior aWrappedSumAgainstItself : (s: StageN, t: StageN) -> Bool
            let aWrappedSumAgainstItself (s, t) = s < t

            behavior quantitiesAgainstEachOther : (a: Amount, b: Amount) -> Bool
            let quantitiesAgainstEachOther (a, b) = a < b

            data Inner = Int
            data Code = Inner
            data Name = String
            data Key = Code | Name

            behavior isSeven : (k: Key) -> Bool
            let isSeven (k) = k == Code(Inner(7))

            behavior aDeepCodeIsSeven : (c: Code) -> Bool
            let aDeepCodeIsSeven (c) = 7 == c
            """;

    @Test
    void twoWholeNumbersAreReadAsTheyStandWhateverTheOperatorAnswers() {
        Core.Binary sum = applying("whole", BinOp.ADD);
        assertInstanceOf(Core.BinaryReading.AsTheyStand.class, sum.reading());
        assertEquals(Type.INT, sum.type());

        Core.Binary quotient = applying("quotient", BinOp.DIV);
        assertInstanceOf(Core.BinaryReading.AsTheyStand.class, quotient.reading());
        assertEquals(Type.INT, quotient.left().type());
        assertEquals(Type.RATIONAL, quotient.type(),
                "the quotient answers an exact value, and that is not how it reads its operands");
    }

    @Test
    void aNumberBesideARationalIsReadAtItsExactValue() {
        Core.Binary sum = applying("exactSum", BinOp.ADD);
        assertSame(Core.BinaryReading.EXACT_NUMBERS, sum.reading());
        assertEquals(Type.INT, sum.left().type(), "the Int is not made a Rational in the tree");
        assertEquals(Type.RATIONAL, sum.right().type());

        Core.Binary equal = applying("exactlyEqual", BinOp.EQ);
        assertSame(Core.BinaryReading.EXACT_NUMBERS, equal.reading());
        assertEquals(Type.DECIMAL, equal.left().type());
    }

    @Test
    void aWholeNumberBesideADecimalIsRefusedWhereTwoDecimalsAreNot() {
        assertEquals(List.of(), errorsOf("d + d"), "the control compiles");
        assertFalse(errorsOf("i + d").isEmpty(),
                "no operator reads an Int and a Decimal, so there is no node to say how");
    }

    @Test
    void aLiteralBesideANewtypeIsReadAsWhatTheNewtypeWrapsAndStaysWhatItIs() {
        Core.Binary compared = applying("underALimit", BinOp.LE);
        Core.BinaryReading.Opened opened = assertInstanceOf(Core.BinaryReading.Opened.class,
                compared.reading());
        assertEquals("Amount", Type.show(opened.newtype()));
        assertEquals(Type.INT, opened.inner());
        assertEquals(Type.INT, compared.right().type(),
                "the literal is an Int, and nothing widened it to stand as the newtype");

        Core.BinaryReading.Opened deep = assertInstanceOf(Core.BinaryReading.Opened.class,
                applying("aDeepCodeIsSeven", BinOp.EQ).reading());
        assertEquals("Code", Type.show(deep.newtype()));
        assertEquals(Type.INT, deep.inner(), "opened through every name it wears");
    }

    /**
     * A newtype a sum lists as a case is a value of that sum as it stands. Beside the sum, the pair
     * is read in the cases both range over and neither side is opened: opened, the {@code Code}
     * would be the {@code Int} it wraps, and no {@code Key} is one.
     */
    @Test
    void aNewtypeBesideTheSumListingItIsReadInTheCasesAndNotOpened() {
        Core.Binary compared = applying("isSeven", BinOp.EQ);
        Core.BinaryReading.In in = assertInstanceOf(Core.BinaryReading.In.class,
                compared.reading());
        Type.Union cases = assertInstanceOf(Type.Union.class, in.type());
        assertEquals(List.of("Code", "Name"),
                cases.members().stream().map(each -> each.name()).toList());
    }

    @Test
    void aNewtypeIsOpenedBesideWhatItWrapsAndNothingElse() {
        Core whole = new Core.Int(1, Type.INT, null);
        Core.BinaryReading.Opened toAWholeNumber =
                assertInstanceOf(Core.BinaryReading.Opened.class,
                        applying("underALimit", BinOp.LE).reading());
        Core decimal = new Core.Decimal(BigDecimal.ONE, Type.DECIMAL, null);
        assertThrows(IllegalArgumentException.class, () -> new Core.Binary(BinOp.EQ, whole,
                decimal, toAWholeNumber, ConstructOccurrence.unwritten(), Type.BOOL, null));
        assertThrows(IllegalArgumentException.class,
                () -> new Core.BinaryReading.Opened(Type.INT, Type.INT));
    }

    @Test
    void aCaseBesideItsSumIsOrderedInTheSumAndComparedInItsCases() {
        Core.BinaryReading.In ordered = assertInstanceOf(Core.BinaryReading.In.class,
                applying("beforeWon", BinOp.LT).reading());
        assertEquals("Stage", Type.show(ordered.type()), "the order belongs to the sum");

        Core.BinaryReading.In equal = assertInstanceOf(Core.BinaryReading.In.class,
                applying("aCircle", BinOp.EQ).reading());
        Type.Union cases = assertInstanceOf(Type.Union.class, equal.type(),
                "sameness is asked across the cases, which no name of either side is");
        assertEquals(List.of("Circle", "Square"),
                cases.members().stream().map(each -> each.name()).toList());
    }

    /** What a comparison reads its operands as and what orders them are two answers. A case
     *  compared with itself reads as the case and is ordered by the sum listing it, while a case
     *  beside its sum reads as the sum: putting the sum in the reading for both would leave a
     *  reader unable to tell a pair that is restated from one that is not. */
    @Test
    void aCaseComparedWithItselfIsReadAsTheCaseAndOrderedByTheSumListingIt() {
        Core.Binary itself = applying("aCaseAgainstItself", BinOp.LE);
        assertInstanceOf(Core.BinaryReading.AsTheyStand.class, itself.reading());
        assertEquals("Won", Type.show(itself.left().type()));
        assertEquals("Stage", orderedBy(itself));

        Core.Binary beside = applying("beforeWon", BinOp.LT);
        Core.BinaryReading.In in = assertInstanceOf(Core.BinaryReading.In.class, beside.reading());
        assertEquals("Stage", Type.show(in.type()));
        assertEquals("Stage", orderedBy(beside),
                "the sum orders both, and reading them in it is a different answer");
    }

    @Test
    void aUnionOfCasesIsOrderedByTheSumListingThemAll() {
        Core.Binary union = applying("casesOfOneSum", BinOp.LT);
        assertInstanceOf(Core.BinaryReading.AsTheyStand.class, union.reading());
        assertInstanceOf(Type.Union.class, union.left().type());
        assertEquals("Stage", orderedBy(union));
    }

    @Test
    void aSumAndANewtypeOverItAreOrderedByTheSum() {
        assertEquals("Stage", orderedBy(applying("aSumAgainstItself", BinOp.LT)));

        Core.Binary wrapped = applying("aWrappedSumAgainstItself", BinOp.LT);
        assertEquals("StageN", Type.show(wrapped.left().type()),
                "the operands stay the newtype, which is nominal");
        assertEquals("Stage", orderedBy(wrapped));
    }

    @Test
    void aQuantityIsOrderedByWhatItWraps() {
        assertEquals("Int", orderedBy(applying("quantitiesAgainstEachOther", BinOp.LT)));
        assertEquals("Int", orderedBy(applying("underALimit", BinOp.LE)));
    }

    @Test
    void anOperatorThatOrdersNothingHasNothingToBeOrderedBy() {
        assertEquals(Optional.empty(), applying("aCircle", BinOp.EQ).ordering());
        assertEquals(Optional.empty(), applying("whole", BinOp.ADD).ordering());
    }

    @Test
    void aWrittenComparisonWithNothingToOrderItIsRefused() {
        Core whole = new Core.Int(1, Type.INT, null);
        ConstructOccurrence written = applying("aCaseAgainstItself", BinOp.LE).occurrence();
        assertThrows(IllegalArgumentException.class, () -> new Core.Binary(BinOp.LT, whole, whole,
                Core.BinaryReading.AS_THEY_STAND, Optional.empty(), written, Type.BOOL, null));
        assertThrows(IllegalArgumentException.class, () -> new Core.Binary(BinOp.EQ, whole, whole,
                Core.BinaryReading.AS_THEY_STAND, Optional.of(new Core.OrderingBasis(Type.INT)),
                ConstructOccurrence.unwritten(), Type.BOOL, null));
    }

    /** What the checker settled orders the operands of {@code compared}, as the type it names. */
    private static String orderedBy(Core.Binary compared) {
        return Type.show(compared.ordering().orElseThrow().type());
    }

    @Test
    void listsJoinedAtOneElementAreReadAsTheyStand() {
        Core.Binary joined = applying("appended", BinOp.CONCAT);
        assertInstanceOf(Core.BinaryReading.AsTheyStand.class, joined.reading());
        assertInstanceOf(Core.Widen.class, joined.left(),
                "standing as the joined list is the Widen's to say, not the reading's");
    }

    @Test
    void newtypeArithmeticIsTheOperationOverWhatTheNewtypesWrap() {
        Core.Construct built = assertInstanceOf(Core.Construct.class, body("doubled"));
        Core.Binary inside = assertInstanceOf(Core.Binary.class,
                built.values().getFirst().value());
        assertInstanceOf(Core.BinaryReading.AsTheyStand.class, inside.reading());
        assertInstanceOf(Core.FieldAccess.class, inside.left());
        assertEquals(Type.INT, inside.type());
    }

    @Test
    void aReadingIsKeptAcrossARewrite() {
        Core.Binary compared = applying("underALimit", BinOp.LE);
        Core.Int other = new Core.Int(200, Type.INT, compared.pos());
        Core.Binary rewritten = assertInstanceOf(Core.Binary.class,
                Core.mapChildren(compared, e -> e == compared.right() ? other : e, r -> r,
                        c -> c));
        assertEquals(compared.reading(), rewritten.reading());
    }

    @Test
    void operandsReadAsTheyStandStandAsOneType() {
        Core whole = new Core.Int(1, Type.INT, null);
        Core decimal = new Core.Decimal(BigDecimal.ONE, Type.DECIMAL, null);
        assertThrows(IllegalArgumentException.class, () -> new Core.Binary(BinOp.ADD, whole,
                decimal, Core.BinaryReading.AS_THEY_STAND, ConstructOccurrence.unwritten(),
                Type.DECIMAL, null));
    }

    private static Core.Binary applying(String behavior, BinOp op) {
        List<Core.Binary> found = new ArrayList<>();
        collect(body(behavior), found);
        List<Core.Binary> applied = found.stream().filter(each -> each.op() == op).toList();
        assertEquals(1, applied.size(), "`" + behavior + "` applies " + op + " once");
        return applied.getFirst();
    }

    private static List<String> errorsOf(String sum) {
        Compilation compilation = Compilation.ofSource("""
                module demo

                behavior mixed : (i: Int, d: Decimal) -> Decimal
                let mixed (i, d) = %s
                """.formatted(sum), "Main");
        compilation.answerEverything();
        return compilation.errors().stream()
                .map(each -> each.diagnostic().code().toString())
                .toList();
    }

    private static void collect(Core e, List<Core.Binary> out) {
        if (e instanceof Core.Binary b) {
            out.add(b);
        }
        Core.forEachChild(e, child -> collect(child, out));
    }

    private static Core body(String behavior) {
        Core body = bodies().behaviorBodies().get(behavior);
        assertNotNull(body, "`" + behavior + "` has a body");
        return Core.withoutStanding(body);
    }

    private static Bodies.Elaborated checked;

    private static Bodies.Elaborated bodies() {
        if (checked != null) {
            return checked;
        }
        Compilation compilation = Compilation.ofSource(MODULE, "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(each -> each.diagnostic().code() + " " + each.diagnostic().primary())
                        .toList(),
                "the model under test compiles");
        checked = compilation.db()
                .ask(new Bodies.Checked(compilation.modules().get(0))).value();
        assertNotNull(checked, "the model under test was checked");
        return checked;
    }
}
