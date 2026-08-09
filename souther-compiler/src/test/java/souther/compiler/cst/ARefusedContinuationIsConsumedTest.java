package souther.compiler.cst;

import souther.compiler.diag.msg.ParseMessage;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What the parser has to say about a narrow type position, all of it.
 *
 * <p>A refused continuation is recognized and then consumed, and the consuming is the half a
 * single-diagnostic test cannot see. {@code Compiler.compile} raises on the first error, so a
 * cascade behind it — the recognition the author needs, followed by the delimiter complaint the
 * displaced tokens caused — reads as a clean answer from there and as noise to everything that
 * takes the whole list. The formatter and the language server take the whole list.
 *
 * <p>So these read {@link CstParser}'s errors directly. Two things are held: what was refused is
 * said once and by name, and the declaration around it goes on parsing, so a later field or a later
 * declaration in the same file is still read rather than swallowed by recovery.
 */
class ARefusedContinuationIsConsumedTest {

    private static List<String> saidBy(String src) {
        return CstParser.parse(src).errors().stream()
                .map(e -> e.said().getClass().getSimpleName())
                .toList();
    }

    @Test
    void aUnionOnAFieldIsSaidOnceAndTheNextFieldStillReads() {
        assertEquals(List.of("AFieldTypeIsNotAnAnonymousUnion"), saidBy("""
                module demo
                data A = { a: Int }
                data B = { b: Int }
                data X = { u: A | B, n: Int }
                """));
    }

    // The tail of a refused union is read the way the position reads a type, so a form forbidden
    // there is answered as that form too. Read as a bare `typeRef` the `?` would be left standing
    // and `>` would be reported missing — the delimiter complaint this whole change is about,
    // reappearing inside the recovery that was meant to prevent it.
    @Test
    void aForbiddenFormInTheRefusedTailIsAlsoNamed() {
        assertEquals(List.of("AnAnonymousUnionIsNotWrittenInsideAnotherType",
                        "AnOptionalIsNotWrittenInsideAnotherType"),
                saidBy("""
                        module demo
                        data A = { a: Int }
                        data B = { b: Int }
                        let f (xs: List<A | B?>) : Int = 1
                        """));
    }

    @Test
    void aUnionNestedInsideATypeArgumentIsSaidOnceForEachPositionItStandsIn() {
        assertEquals(List.of("AnAnonymousUnionIsNotWrittenInsideAnotherType"), saidBy("""
                module demo
                data A = { a: Int }
                data B = { b: Int }
                let f (xs: List<List<B | A>>) : Int = 1
                """));
    }

    @Test
    void aUnionInATupleMemberLeavesTheRestOfTheTupleReadable() {
        assertEquals(List.of("AnAnonymousUnionIsNotWrittenInsideAnotherType"), saidBy("""
                module demo
                data A = { a: Int }
                data B = { b: Int }
                let f (t: (A | B, Int)) : Int = 1
                """));
    }

    @Test
    void aRefusedFieldDoesNotSwallowTheDeclarationAfterIt() {
        assertEquals(List.of("AFieldTypeIsNotAnAnonymousUnion"), saidBy("""
                module demo
                data A = { a: Int }
                data B = { b: Int }
                data X = { u: A | B }
                data Y = { n: Int }
                """));
    }

    // Nothing is said where the forms these positions take are written.
    @Test
    void theFormsThesePositionsTakeSayNothing() {
        assertEquals(List.of(), saidBy("""
                module demo
                data A = { a: Int }
                data X = { x: Int?, one: A }
                let f (xs: List<Option<Int>>, t: (Option<Int>, A)) : Int = 1
                """));
    }

    // A reference for the reading above: the message records exist and are what those names are.
    @Test
    void theNamesAboveAreTheRecordsThemselves() {
        assertEquals("AFieldTypeIsNotAnAnonymousUnion",
                ParseMessage.AFieldTypeIsNotAnAnonymousUnion.class.getSimpleName());
        assertEquals("AnAnonymousUnionIsNotWrittenInsideAnotherType",
                ParseMessage.AnAnonymousUnionIsNotWrittenInsideAnotherType.class.getSimpleName());
        assertEquals("AnOptionalIsNotWrittenInsideAnotherType",
                ParseMessage.AnOptionalIsNotWrittenInsideAnotherType.class.getSimpleName());
    }
}
