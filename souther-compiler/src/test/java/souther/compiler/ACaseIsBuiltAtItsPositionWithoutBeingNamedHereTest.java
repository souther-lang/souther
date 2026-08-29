package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.meta.ModulePath;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A value is built in the form the position reads it, and the position is a type — not a name this
 * module happens to have.
 *
 * <p>A derived decoder dispatches over the leaves of the sums it names (spec §sum-discrimination), so
 * a behavior taking `離職事由` is filled with values of leaves the module never writes: it matches on
 * `事業主都合`, and which kind of employer cause it was is a question its own rules do not ask. The
 * leaf is a case of the position all the same, and a fixture for it is a fixture of that position.
 *
 * <p>Held across two modules because that is the only place the two ways of asking come apart. Asked
 * of the position's declared type, the leaf is listed by its decoder and carries the tag that decoder
 * reads. Asked of the leaf's own spelling, the answer is what the reading module has under that
 * spelling — nothing here — and the value went out with no discriminator on it and was refused for
 * the key it was missing (issue #683).
 *
 * <p>Being a case of the position is not being writable at it. {@code domain} exposes the sum and
 * not its cases, so no spelling here reaches {@code 事業主都合}'s leaves — not the bare name, and not
 * the qualified one either. The class is still a class and a row already sitting in it still covers
 * it; what cannot be offered is a new row, and the reason belongs to the model rather than to this
 * generator. Offered anyway, the row was a name out of scope wherever it was pasted (issue #696).
 */
class ACaseIsBuiltAtItsPositionWithoutBeingNamedHereTest {

    private static final String DOMAIN = """
            module domain exposing (Reason, EmployerCause, Resignation)

            data BusinessClosure
            data Dismissal
            data EmployerCause = BusinessClosure | Dismissal

            data Resignation = { note: String }

            data Reason = EmployerCause | Resignation
            """;

    /** Names `EmployerCause` and never its cases: the rule here is about the group. */
    private static final String CONSUMER = """
            module consumer

            import domain (Reason, EmployerCause, Resignation)

            data Verdict = { text: String }

            behavior judge : (reason: Reason) -> Verdict
                constructs Verdict

            let judge (reason) =
                match reason with
                    | EmployerCause -> Verdict { text = "employer" }
                    | Resignation   -> Verdict { text = "resigned" }
            """;

    private static souther.compiler.partition.FillResult filled() {
        Compilation compilation = Compilation.ofSources(List.of(DOMAIN, CONSUMER), ModulePath.EMPTY);
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, Adequacy.Filling> all = Adequacy.generatedOf(compilation.db(), "consumer");
        assertNotNull(all, "the model under test compiles");
        return all.get("judge").composed();
    }

    @Test
    void aLeafThisModuleCanNameGetsARowAndTheOthersGetTheirReason() {
        souther.compiler.partition.FillResult filled = filled();

        assertEquals(List.of("Resignation { note = \"x\" }"),
                filled.rows().stream()
                        .map(r -> String.join(", ", r.inputs().stream().map(i -> i.text()).toList()))
                        .toList());
        assertEquals(List.of(
                        "`domain` does not expose `BusinessClosure`, so nothing here can name it",
                        "`domain` does not expose `Dismissal`, so nothing here can name it"),
                filled.unresolved().stream().map(u -> u.said().orElseThrow()).toList(),
                "each case of the position that has no name here says so");
    }
}
