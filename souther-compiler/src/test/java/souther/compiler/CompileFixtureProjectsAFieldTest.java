package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A field taken off a value a row can already build. A spread copies every field of such a value and
 * was admitted; reading one of them back was not, so a fixture for a collection derived from another
 * value had to be written out again as a literal.
 *
 * <p>What a taken field supplies is its declaration's to say — which is the answer a value cannot
 * give where the field holds an empty collection, there being no element to name. Where the value is
 * one a helper answered with, the answer says it, as it does wherever a helper stands.
 */
class CompileFixtureProjectsAFieldTest {

    @Test
    void anExpectedValueReadsAFieldOffANamedValue() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo

                data Line = { done: Bool }
                data Ticket = { lines: List<Line> }

                let sample = Ticket { lines = [ Line { done = false } ] }

                behavior linesOf : (t: Ticket) -> List<Line>
                let linesOf (t) = t.lines

                example linesOf
                    | "an expected value reads a field" : (sample) -> sample.lines
                """));
    }

    /**
     * The case a value cannot answer. An empty list has no element to name, so what says the field
     * supplies a {@code List<AmountN>} is the declaration and nothing else.
     */
    @Test
    void aProjectedEmptyCollectionIsHeldToTheFieldsDeclaration() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data AmountN = Int
                data Basket = { amounts: List<AmountN> }

                let empty = Basket { amounts = [ ] }

                behavior countOf : (ns: List<Int>) -> Int
                let countOf (ns) = List.length(ns)

                example countOf
                    | "an empty list keeps the name its field declares" : (empty.amounts) -> 0
                """));
        // The reason and not the code: a fixture that cannot be read at all is E1903 too, so a row
        // asserting the code alone goes green while nothing has been held to any declaration.
        assertTrue(e.getMessage().contains("List<AmountN>") && e.getMessage().contains("List<Int>"),
                e.getMessage());
    }

    /** The control for the above: the same projection at the position its field declares. */
    @Test
    void aProjectedCollectionIsAdmittedAtItsOwnDeclaration() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo

                data AmountN = Int
                data Basket = { amounts: List<AmountN> }

                let empty = Basket { amounts = [ ] }

                behavior countOf : (ns: List<AmountN>) -> Int
                let countOf (ns) = List.length(ns)

                example countOf
                    | "the same declaration is admitted" : (empty.amounts) -> 0
                """));
    }

    @Test
    void aProjectedValueIsAdmittedWhereAnOptionalHoldsIt() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo

                data AmountN = Int
                data Basket = { total: AmountN }
                data Order = { total: AmountN? }

                let one = Basket { total = AmountN(100) }

                behavior hasTotal : (o: Order) -> Bool
                let hasTotal (o) = true

                example hasTotal
                    | "an optional field holds what a field declares" : (Order { total = one.total }) -> true
                """));
    }

    @Test
    void aFieldIsTakenOffWhatAHelperAnswered() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo

                data Line = { done: Bool }
                data Ticket = { lines: List<Line> }

                let sample = Ticket { lines = [ Line { done = false } ] }
                let markDone (t: Ticket) = Ticket { lines = List.map(l -> Line { ...l, done = true }, t.lines) }

                behavior allDone : (ls: List<Line>) -> Bool
                let allDone (ls) = List.all(l -> l.done, ls)

                example allDone
                    | "a field off a helper's answer" : (markDone(sample).lines) -> true
                """));
    }

    /** No declaration of this module's says what a helper answered, so the answer must. */
    @Test
    void aFieldTakenOffAHelpersAnswerIsAdmittedAtItsPosition() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data AmountN = Int
                data Basket = { total: AmountN }

                let makeBasket (n: Int) = Basket { total = AmountN(n) }

                behavior isHundred : (n: Int) -> Bool
                let isHundred (n) = n == 100

                example isHundred
                    | "a helper's field is held to the position it stands at" : (makeBasket(100).total) -> true
                """));
        assertTrue(e.getMessage().contains("AmountN") && e.getMessage().contains("Int"),
                e.getMessage());
    }

    /** The same, reached through a name. A value whose body is a helper application is nameable, so
     *  the closure rule covers it and the evidence must survive the name. */
    @Test
    void aFieldTakenOffANamedHelperAnswerIsAdmittedAtItsPosition() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data AmountN = Int
                data Basket = { total: AmountN }

                let makeBasket (n: Int) = Basket { total = AmountN(n) }
                let basket = makeBasket(100)

                behavior isHundred : (n: Int) -> Bool
                let isHundred (n) = n == 100

                example isHundred
                    | "a field off a named helper answer keeps its runtime name" : (basket.total) -> true
                """));
        assertTrue(e.getMessage().contains("AmountN") && e.getMessage().contains("Int"),
                e.getMessage());
    }

    /** The control for the two above: an implementation that refused every projection off a helper
     *  answer would satisfy them both. */
    @Test
    void aFieldIsTakenOffANamedHelperAnswer() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo

                data AmountN = Int
                data Basket = { total: AmountN }

                let makeBasket (n: Int) = Basket { total = AmountN(n) }
                let basket = makeBasket(100)

                behavior isHundred : (a: AmountN) -> Bool
                let isHundred (a) = a.value == 100

                example isHundred
                    | "the same field at its own declaration" : (basket.total) -> true
                """));
    }

    /** The rule is recursive on its own conclusion, so what a helper answered is still its answer at
     *  the second field. A value that has been through a neutral form no longer says what it is. */
    @Test
    void aProjectionOfAProjectionKeepsTheAnswersName() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data AmountN = Int
                data Inner = { total: AmountN }
                data Outer = { inner: Inner }

                let makeOuter (n: Int) = Outer { inner = Inner { total = AmountN(n) } }

                behavior isHundred : (n: Int) -> Bool
                let isHundred (n) = n == 100

                example isHundred
                    | "projection remains live through another projection" :
                        (makeOuter(100).inner.total) -> true
                """));
        assertTrue(e.getMessage().contains("AmountN") && e.getMessage().contains("Int"),
                e.getMessage());
    }

    /** The declared chain, which reaches no helper: each step must descend, not only the first. */
    @Test
    void aDeclaredProjectionChainIsHeldAtEachStep() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data AmountN = Int
                data Inner = { total: AmountN }
                data Outer = { inner: Inner }

                let outer = Outer { inner = Inner { total = AmountN(100) } }

                behavior isHundred : (n: Int) -> Bool
                let isHundred (n) = n == 100

                example isHundred
                    | "a declared chain is held at its last step" : (outer.inner.total) -> true
                """));
        assertTrue(e.getMessage().contains("AmountN") && e.getMessage().contains("Int"),
                e.getMessage());
    }

    // --- a newtype declares one field, and it is what it wraps -----------------------------------

    @Test
    void aNewtypeWrappedValueIsReadAsItsField() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo

                data AmountN = Int

                let listed = AmountN(100)

                behavior isHundred : (n: Int) -> Bool
                let isHundred (n) = n == 100

                example isHundred
                    | "what a newtype wraps is a field" : (listed.value) -> true
                """));
    }

    @Test
    void aNewtypeAnsweredByAHelperIsReadAsItsField() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo

                data AmountN = Int

                let makeAmount (n: Int) = AmountN(n)

                behavior isHundred : (n: Int) -> Bool
                let isHundred (n) = n == 100

                example isHundred
                    | "project a newtype returned by a helper" : (makeAmount(100).value) -> true
                """));
    }

    @Test
    void aNamedNewtypeAnswerIsStillANewtypeWhenProjected() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo

                data AmountN = Int

                let makeAmount (n: Int) = AmountN(n)
                let amount = makeAmount(100)

                behavior isHundred : (n: Int) -> Bool
                let isHundred (n) = n == 100

                example isHundred
                    | "a named helper answer is still a newtype when projected" : (amount.value) -> true
                """));
    }

    /** What `.value` supplies is the base, so it does not supply the newtype. Without this, a walk
     *  that never recognised the construction at all would satisfy the three above. */
    @Test
    void aNewtypeFieldStatesItsBaseType() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data AmountN = Int

                behavior takesAmount : (n: AmountN) -> Bool
                let takesAmount (n) = true

                example takesAmount
                    | "a newtype value field is its declared base" : (AmountN(100).value) -> true
                """));
        // The reason and not the code: a fixture that could not be read at all is E1903 too.
        assertTrue(e.getMessage().contains("declaring `Int`")
                && e.getMessage().contains("`AmountN`"), e.getMessage());
    }

    /** The chain that crosses both kinds of evidence: a helper's answer, a field, and the base. */
    @Test
    void aProjectionChainReachesWhatANewtypeWraps() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo

                data AmountN = Int
                data Inner = { total: AmountN }
                data Outer = { inner: Inner }

                let makeOuter (n: Int) = Outer { inner = Inner { total = AmountN(n) } }

                behavior isHundred : (n: Int) -> Bool
                let isHundred (n) = n == 100

                example isHundred
                    | "the chain reaches what the newtype wraps" :
                        (makeOuter(100).inner.total.value) -> true
                """));
    }

    // --- what a field read off a fixture cannot be -----------------------------------------------

    @Test
    void aFieldIsNotTakenOffAValueThatIsNotARecord() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                let listed = 100

                behavior isHundred : (n: Int) -> Bool
                let isHundred (n) = n == 100

                example isHundred
                    | "a number has no field" : (listed.total) -> true
                """));
        assertTrue(e.getMessage().contains("is not a record"), e.getMessage());
    }

    @Test
    void aFieldTheRecordDoesNotDeclareIsRefused() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data Basket = { total: Int }

                let one = Basket { total = 100 }

                behavior isHundred : (n: Int) -> Bool
                let isHundred (n) = n == 100

                example isHundred
                    | "no such field" : (one.missing) -> true
                """));
        assertTrue(e.getMessage().contains("declares no field `missing`"), e.getMessage());
    }

    /** A cycle through a field is reported as the cycle it is. The value graph is checked before a
     *  fixture reads it, so this is E1022's to say and never reaches the reader — the reader's own
     *  check stands behind it, and is one check for both the reading that takes the value and the
     *  walk that types it, so the two cannot report one cycle two ways. */
    @Test
    void aCycleReachedThroughAFieldIsReportedAsACycle() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data Basket = { total: Int }

                let one = Basket { total = other.total }
                let other = Basket { total = one.total }

                behavior isHundred : (n: Int) -> Bool
                let isHundred (n) = n == 100

                example isHundred
                    | "a cycle through a field" : (one.total) -> true
                """));
        assertTrue(e.getMessage().contains("defined in terms of itself"), e.getMessage());
    }
}
