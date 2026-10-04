package souther.compiler.check;

import souther.compiler.Compiler;
import souther.compiler.WhereItSits;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.PhysicalPos;
import souther.compiler.diag.Primary;
import souther.compiler.diag.msg.ArithmeticMessage;
import souther.compiler.diag.msg.AttemptMessage;
import souther.compiler.diag.msg.HelperMessage;
import souther.compiler.diag.msg.MatchMessage;
import souther.compiler.diag.msg.Message;
import souther.compiler.diag.msg.TypeMessage;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * What a library operation is handed in place of a function is reported against the call, in the
 * scope the call is written in, and the report names the operation as the call spells it.
 *
 * <p>The function is typed once, where the elaboration reads it: at the boundary of the call's
 * expansion, where the callee applies it, or against the signature of a call left standing. The
 * report is made there from what the call left behind — the parameter the function was handed to
 * and the call as written. Without that, the same mistake is a value applied, or a block
 * answering, inside a body this compile has no source for. The rows below are the places a binding
 * comes into force — a parameter, a {@code let}, a {@code let} of a {@code let}, and a block's own
 * parameter — and each reaches the report as the name the author wrote.
 *
 * <p>The scope is keyed by the binding and not by its spelling, which only a row with two bindings of
 * one name can tell apart: the inner one is what the call reads, and the outer one is a type the
 * call must not be held to.
 */
class AFunctionArgumentIsCheckedInTheScopeItIsWrittenInTest {

    /** What every call below is written as. */
    private static final String WROTE = "List.map";

    @Test
    void aParameterHandedOverIsReportedAtTheParameter() {
        String source = """
                module m

                behavior f : (xs: List<Int>, k: Int) -> List<Int>
                let f (xs, k) = List.map(k, xs)
                """;

        HelperMessage.AValueWhereAFunctionIsTaken said = aValueWhereAFunctionIsTaken(source, "k");
        assertEquals(WROTE, said.call());
        assertEquals("k", said.written());
    }

    @Test
    void aLetOfAValueHandedOverIsReportedAtTheName() {
        String source = """
                module m

                behavior f : (xs: List<Int>, k: Int) -> List<Int>
                let f (xs, k) = {
                    let j = k
                    List.map(j, xs)
                }
                """;

        HelperMessage.AValueWhereAFunctionIsTaken said = aValueWhereAFunctionIsTaken(source, "j");
        assertEquals(WROTE, said.call());
        assertEquals("j", said.written());
    }

    @Test
    void soIsALetOfThatLet() {
        String source = """
                module m

                behavior f : (xs: List<Int>, k: Int) -> List<Int>
                let f (xs, k) = {
                    let j = k
                    let q = j
                    List.map(q, xs)
                }
                """;

        assertEquals("q", aValueWhereAFunctionIsTaken(source, "q").written());
    }

    /** The block's own parameter is an {@code Int} because the outer call hands it the elements of
     *  a {@code List<Int>}, and nothing but that call says so. */
    @Test
    void aBlocksParameterHandedOverIsReportedAtTheParameter() {
        String source = """
                module m

                behavior f : (xs: List<Int>, ys: List<Int>) -> List<List<Int>>
                let f (xs, ys) = List.map(x -> List.map(x, ys), xs)
                """;

        assertEquals("x", aValueWhereAFunctionIsTaken(source, "x,").written());
    }

    /** What {@code Some} opens is the element, so {@code x} is the {@code Int} the list holds. */
    @Test
    void anOptionArmsBindingHandedOverIsReportedAtTheName() {
        String source = """
                module m

                behavior f : (xs: List<Int>) -> List<Int>
                let f (xs) =
                    match List.get(0, xs) with
                        | Some x -> List.map(x, xs)
                        | None -> xs
                """;

        assertEquals("x", aValueWhereAFunctionIsTaken(source, "x,").written());
    }

    @Test
    void aCaseArmsBindingHandedOverIsReportedAtTheName() {
        String source = """
                module m

                data A = { n: Int }
                data B = { k: Int }
                data S = A | B

                behavior f : (s: S, xs: List<Int>) -> List<Int>
                let f (s, xs) =
                    match s with
                        | A as a -> List.map(a, xs)
                        | B -> xs
                """;

        assertEquals("a", aValueWhereAFunctionIsTaken(source, "a,").written());
    }

    /** An or-pattern binds the subject itself, since no one case's type fits every alternative. */
    @Test
    void anOrPatternsBindingHandedOverIsReportedAtTheName() {
        String source = """
                module m

                data A = { n: Int }
                data B = { k: Int }
                data S = A | B

                behavior f : (s: S, xs: List<Int>) -> List<Int>
                let f (s, xs) =
                    match s with
                        | A | B as v -> List.map(v, xs)
                """;

        assertEquals("v", aValueWhereAFunctionIsTaken(source, "v,").written());
    }

    /** The value an attempted construction built is in force over the branch it succeeds into. */
    @Test
    void whatAnAttemptBuiltHandedOverIsReportedAtTheName() {
        String source = """
                module m

                data Pos = Int
                    invariant positive = value >= 1

                behavior f : (n: Int, xs: List<Int>) -> List<Int>
                    constructs Pos
                let f (n, xs) =
                    if Pos(n) as p then List.map(p, xs) else xs
                """;

        assertEquals("p", aValueWhereAFunctionIsTaken(source, "p,").written());
    }

    /**
     * A block whose body does not type still has the parameters the position gives it, since what
     * they are is the position's and not the body's. So a mistake the check can name inside it is
     * named, as one is anywhere else in a body that also holds a mistake only the elaboration can
     * name: the check reads the whole body before the elaboration reads any of it. The call is in
     * what the binding is given, which is read wherever the binding is written, and not under the
     * binding, which the mistake after it does not refuse either.
     */
    @Test
    void insideABlockThatDoesNotTypeTheParametersAreStillInForce() {
        String source = """
                module m

                behavior f : (xs: List<Int>, ys: List<Int>) -> List<List<Int>>
                let f (xs, ys) = List.map(x -> {
                    let mapped = List.map(x, ys)
                    mapped + "one"
                }, xs)
                """;

        assertEquals("x", aValueWhereAFunctionIsTaken(source, "x,").written());
    }

    /**
     * {@code as} names what a construction builds, and {@code n > 0} builds nothing, so there is no
     * {@code c} for the call to be checked against: what is reported is why there is none.
     */
    @Test
    void anAttemptOnWhatIsNotAConstructionBindsNothing() {
        String source = """
                module m

                behavior f : (n: Int, xs: List<Int>) -> List<Int>
                let f (n, xs) = {
                    guard n > 0 as c else xs
                    List.map(c, xs)
                }
                """;

        assertInstanceOf(AttemptMessage.ThisIsNotAConstruction.class,
                refused(source).diagnostic().said());
    }

    @Test
    void anAttemptAtATypeWithNoInvariantBindsNothing() {
        String source = """
                module m

                data Plain = Int

                behavior f : (n: Int, xs: List<Int>) -> List<Int>
                    constructs Plain
                let f (n, xs) =
                    if Plain(n) as p then List.map(p, xs) else xs
                """;

        assertInstanceOf(AttemptMessage.TheTypeDeclaresNoInvariant.class,
                refused(source).diagnostic().said());
    }

    @Test
    void aLetOpeningWhatIsNotANewtypeBindsNothing() {
        String source = """
                module m

                data Line = { sku: String, qty: Int }

                behavior f : (l: Line, xs: List<Int>) -> List<Int>
                let f (l, xs) = {
                    let Line(x) = l
                    List.map(x, xs)
                }
                """;

        assertInstanceOf(TypeMessage.NotANewtypeToOpenInABinding.class,
                refused(source).diagnostic().said());
    }

    @Test
    void aLetOpeningAnotherNewtypeBindsNothing() {
        String source = """
                module m

                data Tags = List<String>
                data Labels = List<String>

                behavior f : (t: Tags, xs: List<Int>) -> List<Int>
                let f (t, xs) = {
                    let Labels(x) = t
                    List.map(x, xs)
                }
                """;

        assertInstanceOf(TypeMessage.ThePatternOpensAnotherType.class,
                refused(source).diagnostic().said());
    }

    /** {@code A} has a field called {@code value}, so reading what the pattern names types; what
     *  the pattern opens is still no newtype. */
    @Test
    void anArmOpeningWhatIsNotANewtypeBindsNothing() {
        String source = """
                module m

                data A = { value: Int }
                data B = { k: Int }
                data S = A | B

                behavior f : (s: S, xs: List<Int>) -> List<Int>
                let f (s, xs) =
                    match s with
                        | A(v) -> List.map(v, xs)
                        | B -> xs
                """;

        assertInstanceOf(MatchMessage.NotANewtypeToOpen.class, refused(source).diagnostic().said());
    }

    /** The element is a {@code Count}, which wraps an {@code Int} as {@code Amount} does, so what the
     *  pattern opens types; it is still not the newtype the element is. */
    @Test
    void anOptionArmOpeningAnotherTypeBindsNothing() {
        String source = """
                module m

                data Amount = Int
                data Count = Int

                behavior f : (cs: List<Count>, xs: List<Int>) -> List<Int>
                let f (cs, xs) =
                    match List.get(0, cs) with
                        | Some(Amount(v)) -> List.map(v, xs)
                        | None -> xs
                """;

        assertInstanceOf(MatchMessage.TheNewtypeWrapsAnotherType.class,
                refused(source).diagnostic().said());
    }

    // Where the language refuses what brings a binding into force, what it governs is never read,
    // so there is no scope to check a call in — not the one around it either. Each row below hands
    // over `k`, a value known outside the refused construct, so a check that read the construct's
    // body in the scope around it would name `k` ahead of the refusal.

    @Test
    void aRefusedAttemptLeavesItsBranchUnread() {
        String source = """
                module m

                behavior f : (n: Int, k: Int, xs: List<Int>) -> List<Int>
                let f (n, k, xs) = {
                    guard n > 0 as c else xs
                    List.map(k, xs)
                }
                """;

        assertInstanceOf(AttemptMessage.ThisIsNotAConstruction.class,
                refused(source).diagnostic().said());
    }

    @Test
    void andItsDeparturesUnreadToo() {
        String source = """
                module m

                behavior f : (n: Int, k: Int, xs: List<Int>) -> List<Int>
                let f (n, k, xs) =
                    if n > 0 as c then xs else List.map(k, xs)
                """;

        assertInstanceOf(AttemptMessage.ThisIsNotAConstruction.class,
                refused(source).diagnostic().said());
    }

    @Test
    void aRefusedLetLeavesItsBodyUnread() {
        String source = """
                module m

                data Line = { sku: String, qty: Int }

                behavior f : (l: Line, k: Int, xs: List<Int>) -> List<Int>
                let f (l, k, xs) = {
                    let Line(x) = l
                    List.map(k, xs)
                }
                """;

        assertInstanceOf(TypeMessage.NotANewtypeToOpenInABinding.class,
                refused(source).diagnostic().said());
    }

    @Test
    void anArmOpeningWhatIsNotANewtypeLeavesItsBodyUnread() {
        String source = """
                module m

                data A = { value: Int }
                data B = { k: Int }
                data S = A | B

                behavior f : (s: S, k: Int, xs: List<Int>) -> List<Int>
                let f (s, k, xs) =
                    match s with
                        | A(v) -> List.map(k, xs)
                        | B -> xs
                """;

        assertInstanceOf(MatchMessage.NotANewtypeToOpen.class, refused(source).diagnostic().said());
    }

    @Test
    void anArmNamingNoCaseLeavesItsBodyUnread() {
        String source = """
                module m

                data A = { n: Int }
                data B = { k: Int }
                data C = { c: Int }
                data S = A | B

                behavior f : (s: S, k: Int, xs: List<Int>) -> List<Int>
                let f (s, k, xs) =
                    match s with
                        | C -> List.map(k, xs)
                        | A -> xs
                        | B -> xs
                """;

        assertInstanceOf(MatchMessage.NotACaseOf.class, refused(source).diagnostic().said());
    }

    @Test
    void aMatchWhoseSubjectDoesNotTypeLeavesItsArmsUnread() {
        String source = """
                module m

                behavior f : (n: Int, k: Int, xs: List<Int>) -> List<Int>
                let f (n, k, xs) =
                    match n + "one" with
                        | Some x -> List.map(k, xs)
                        | None -> xs
                """;

        assertInstanceOf(ArithmeticMessage.AnOperandIsNotANumber.class,
                refused(source).diagnostic().said());
    }

    /** The inner {@code j} holds a function and the outer one an {@code Int}. A scope that found the
     *  name by its spelling would hold the call to the outer one and refuse it. */
    @Test
    void aLetOfAFunctionIsNotReadAsTheValueItShadows() {
        String source = """
                module m

                let f (xs: List<Int>, j: Int, g: (Int) -> Int): List<Int> = {
                    let j = g
                    List.map(j, xs)
                }

                behavior go : (xs: List<Int>) -> List<Int>
                let go (xs) = f(xs, 1, x -> x + 1)
                """;

        assertDoesNotThrow(() -> Compiler.compile(source));
    }

    /** A value that does not type is the elaboration's to report, as it is with no call after it. */
    @Test
    void aLetWhoseValueDoesNotTypeIsReportedAsThatAndNotAsTheCall() {
        String source = """
                module m

                behavior f : (xs: List<Int>, k: Int) -> List<Int>
                let f (xs, k) = {
                    let j = k + "one"
                    List.map(j, xs)
                }
                """;

        assertInstanceOf(ArithmeticMessage.AnOperandIsNotANumber.class,
                refused(source).diagnostic().said());
    }

    @Test
    void aBlockOfAnotherArityNamesTheOperationAsWritten() {
        String source = """
                module m

                behavior f : (xs: List<Int>) -> List<Int>
                let f (xs) = List.map((a, b) -> a, xs)
                """;

        Message said = refused(source).diagnostic().said();
        assertEquals(WROTE,
                assertInstanceOf(HelperMessage.TheBlockTakesAnotherNumberOfArguments.class, said)
                        .call());
    }

    @Test
    void aBlockAnsweringAnotherTypeNamesTheOperationAsWritten() {
        String source = """
                module m

                behavior f : (xs: List<Int>) -> List<Int>
                let f (xs) = List.filterMap(x -> x + 1, xs)
                """;

        Message said = refused(source).diagnostic().said();
        HelperMessage.TheBlockAnswersAnotherType answers =
                assertInstanceOf(HelperMessage.TheBlockAnswersAnotherType.class, said);
        assertEquals("List.filterMap", answers.call());
        assertEquals("Int", answers.returns());
    }

    /** What the call has not decided is shown as the variable the parameter declared, and what it
     *  has decided is written in: {@code 'a} is the element, {@code 'b} is still open. */
    @Test
    void whatTheParameterDeclaredIsShownInItsOwnVariables() {
        String source = """
                module m

                behavior f : (xs: List<Int>) -> List<Int>
                let f (xs) = List.filterMap(x -> x + 1, xs)
                """;

        HelperMessage.TheBlockAnswersAnotherType answers = assertInstanceOf(
                HelperMessage.TheBlockAnswersAnotherType.class,
                refused(source).diagnostic().said());
        assertEquals("'b?", answers.must());
    }

    // A recursive helper is not expanded: its calls stand, typed against its signature. What it
    // is handed is reported in the same words as at a call that is expanded, naming the parameter
    // its declaration wrote.

    /** What every call below is to. */
    private static final String TIMES = """
            module m

            partial let times (step: (Int) -> Int, x: Int, k: Int): Int =
                if k == 0 then x else times(step, step(x), k - 1)

            behavior g : (n: Int) -> Int
            """;

    @Test
    void aValueHandedToARecursiveHelperIsReportedAtTheName() {
        HelperMessage.AValueWhereAFunctionIsTaken said = assertInstanceOf(
                HelperMessage.AValueWhereAFunctionIsTaken.class,
                refused(TIMES + "let g (n) = times(n, n, 3)\n").diagnostic().said());
        assertEquals("step", said.parameter());
        assertEquals("times", said.call());
        assertEquals("n", said.written());
    }

    @Test
    void aBlockAnsweringAnotherTypeToARecursiveHelperNamesItsParameter() {
        HelperMessage.TheBlockAnswersAnotherType said = assertInstanceOf(
                HelperMessage.TheBlockAnswersAnotherType.class,
                refused(TIMES + "let g (n) = times(x -> \"one\", n, 3)\n").diagnostic().said());
        assertEquals("step", said.parameter());
        assertEquals("times", said.call());
        assertEquals("Int", said.must());
        assertEquals("String", said.returns());
    }

    @Test
    void aBlockOfAnotherArityToARecursiveHelperNamesItsParameter() {
        HelperMessage.TheBlockTakesAnotherNumberOfArguments said = assertInstanceOf(
                HelperMessage.TheBlockTakesAnotherNumberOfArguments.class,
                refused(TIMES + "let g (n) = times((a, b) -> a, n, 3)\n").diagnostic().said());
        assertEquals("step", said.parameter());
        assertEquals("times", said.call());
    }

    @Test
    void aCallOfAnotherArityNamesTheOperationAsWritten() {
        String source = """
                module m

                behavior f : (xs: List<Int>) -> List<Int>
                let f (xs) = List.map(xs)
                """;

        Message said = refused(source).diagnostic().said();
        assertEquals(WROTE,
                assertInstanceOf(HelperMessage.CalledWithAnotherNumberOfArguments.class, said)
                        .call());
    }

    /** The report, held to be the one about a value handed to a function parameter and to start
     *  where {@code at} is first written in the call's line. */
    private static HelperMessage.AValueWhereAFunctionIsTaken aValueWhereAFunctionIsTaken(
            String source, String at) {
        CompileException e = refused(source);
        HelperMessage.AValueWhereAFunctionIsTaken said = assertInstanceOf(
                HelperMessage.AValueWhereAFunctionIsTaken.class, e.diagnostic().said(),
                () -> "refused as something else: " + e.getMessage());
        PhysicalPos start = WhereItSits.in(source,
                ((Primary.InSource) e.diagnostic().primary()).place().region()).start();
        String[] lines = source.split("\n", -1);
        int line = lastLineCalling(lines);
        assertEquals(line + 1, start.line(), () -> "reported on another line: " + e.getMessage());
        assertEquals(lines[line].indexOf(at, lines[line].indexOf(WROTE)) + 1, start.column(),
                () -> "reported at another column: " + e.getMessage());
        return said;
    }

    /** The line the innermost call is written on. */
    private static int lastLineCalling(String[] lines) {
        for (int i = lines.length - 1; i >= 0; i--) {
            if (lines[i].contains(WROTE)) {
                return i;
            }
        }
        throw new IllegalArgumentException("no line calls " + WROTE);
    }

    private static CompileException refused(String source) {
        return assertThrows(CompileException.class, () -> Compiler.compile(source));
    }
}
