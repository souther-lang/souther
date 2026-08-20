package souther.compiler;

import souther.compiler.diag.msg.ParseMessage;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * No type position answers a written type form with the delimiter it wanted next.
 *
 * <p>This is the invariant #522 was one cell of. A position that reads a narrow type production
 * refuses some forms in the grammar, which is a decision about the language; what does not follow
 * from it is that the refusal has to be reported as a missing `}` or `>`. Where nothing recognizes
 * the form, delimiter recovery is all that is left, and what the author reached for is gone from
 * the answer — so the same misconception got a repair in one position and a token complaint in
 * another, decided by which production the position happened to call.
 *
 * <p>The quantifier is every type position the specification names
 * (`a-type-is-written-in-a-type-position`) crossed with every type form the type position admits
 * somewhere, and the question asked of each cell is only whether the answer is about the form.
 * Which code it carries, and whether it is refused at all, is each position's own business and is
 * held elsewhere. Some cells fail on the value rather than the type, and that is fine: those are
 * answers about something, which is the whole of what this asks.
 *
 * <p>Two things are pinned besides, because a sweep this wide can go quiet without saying so. Every
 * position must take at least one of the forms: a source that never compiles is not a probe of the
 * position but a template failing for a reason of its own, and it would answer this test whatever
 * the parser did — four of these were exactly that when the positions were first written out. And
 * the number of refused cells is fixed, so the first assertion cannot come to hold by everything
 * compiling. That number says nothing about *which* cells refuse; a change to it is a change to
 * what some position admits, to be read rather than re-fitted.
 *
 * <p>Against the compiler as it stood before the recognition was added, five cells answered with a
 * delimiter: a `|` on a data field, and a `|` and a `?` in each of a type argument and a tuple's
 * member.
 */
class NoTypePositionAnswersWithADelimiterTest {

    /** A form the type position admits somewhere, with something of that type to write. */
    private record Form(String type, String value) {}

    /** The forms, each with something of it to write where a position needs a value. */
    private static final List<Form> FORMS = List.of(
            new Form("A | B", "A { a = 1 }"),
            new Form("Int?", "1"),
            new Form("(Int, Int)", "(1, 1)"),
            new Form("(Int) -> Int", "(x) -> x + 1"),
            new Form("List<Int>", "[1]"),
            new Form("A", "A { a = 1 }"));

    /**
     * How many of the {@link TypePositions#ALL} × {@link #FORMS} cells are refused at all. Pinned so the
     * delimiter assertion cannot come to pass by everything compiling; what refuses what is elsewhere.
     */
    private static final int REFUSED = 36;

    /** Whether the answer names the delimiter the reading stopped at rather than what was written. */
    private static boolean isDelimiterComplaint(Diagnostic d) {
        return d.said() instanceof ParseMessage.ADeclarationExpectedSomethingElse
                || d.said() instanceof ParseMessage.AnExpressionExpectedSomethingElse
                || d.said() instanceof ParseMessage.APatternExpectedSomethingElse
                || d.said() instanceof ParseMessage.AnExampleExpectedSomethingElse;
    }

    @Test
    void everyTypeFormIsAnsweredAboutWhereverItIsWritten() {
        List<String> bare = new ArrayList<>();
        List<String> neverCompiles = new ArrayList<>();
        int refused = 0;
        for (TypePositions.Position position : TypePositions.ALL) {
            int accepted = 0;
            for (Form form : FORMS) {
                try {
                    Compiler.compile(position.of(form.type(), form.value()));
                    accepted++;
                } catch (CompileException e) {
                    refused++;
                    if (isDelimiterComplaint(e.diagnostic())) {
                        bare.add(position.name() + " <- " + form.type()
                                + "  ->  " + e.diagnostic().code());
                    }
                }
            }
            if (accepted == 0) {
                neverCompiles.add(position.name());
            }
        }
        assertEquals(List.of(), neverCompiles,
                "a position took none of the forms, so what it answers about them says nothing");
        assertEquals(List.of(), bare,
                "a type position answered a written type form with the delimiter it wanted next");
        assertEquals(REFUSED, refused,
                "the cells that refuse a form are what they were; read the change rather than re-fitting");
    }
}
