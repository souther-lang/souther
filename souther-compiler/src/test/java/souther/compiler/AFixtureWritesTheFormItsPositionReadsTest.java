package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.observe.Disposition;
import souther.compiler.observe.FailurePhase;
import souther.compiler.observe.RowOutcome;
import souther.compiler.query.Compilation;
import souther.compiler.query.Output;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A fixture is written in the form the position's own decoder reads. For a newtype that some sum also
 * lists, that form depends on the position: read as a case of the sum it wears the {@code "value"}
 * envelope beside the discriminator, and read as itself it is its bare inner value — because the
 * envelope is what membership adds and not part of the newtype's representation (spec 10.3).
 *
 * <p>Both positions are written here, since the form is right in one of them under either rule and a
 * row that only ever stands in a sum cannot tell the two apart.
 */
class AFixtureWritesTheFormItsPositionReadsTest {

    private static final String MODEL = """
            module example.envelope

            data Address = String
            data Activated = Address
            data Pending = Address
            data Mail = Activated | Pending

            data Member = { mail: Mail }
            data Sent = { to: Address }

            behavior notify : (to: Activated) -> Sent constructs Sent
            let notify (to) = Sent { to = to.value }

            behavior reach : (member: Member) -> Sent constructs Sent
            let reach (member) = match member.mail with
                | Activated as a -> Sent { to = a.value }
                | Pending as p   -> Sent { to = p.value }
            """;

    private static List<RowOutcome> rowsOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        Output.Examples key = Output.Examples.asked(compilation.db(),
                compilation.modules().get(0), compilation.sourceIds().get(0));
        Output.Examples.Of answer = compilation.db().ask(key).value();
        assertNotNull(answer, "the answer carries what the rows observed");
        return answer.rows();
    }

    private static void assertTheRowHeld(String example) {
        List<RowOutcome> rows = rowsOf(MODEL + example);
        assertEquals(1, rows.size(), rows.toString());
        assertEquals(Disposition.HELD, rows.get(0).disposition(), rows.get(0).toString());
        assertEquals(FailurePhase.NONE, rows.get(0).failurePhase());
    }

    @Test
    void aNewtypeWrittenAtItsOwnTypeIsItsInnerValue() {
        assertTheRowHeld("""

                example notify
                    | "the parameter is the case itself" :
                        (Activated(Address("a@example.com"))) -> Sent { to = Address("a@example.com") }
                """);
    }

    @Test
    void aNewtypeWrittenAtASumThatListsItWearsTheEnvelope() {
        assertTheRowHeld("""

                example reach
                    | "the field is the sum" :
                        (Member { mail = Activated(Address("a@example.com")) })
                            -> Sent { to = Address("a@example.com") }
                """);
    }
}
