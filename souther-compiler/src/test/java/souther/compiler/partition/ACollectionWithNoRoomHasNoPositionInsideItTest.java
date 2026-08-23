package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A class at a position inside a collection the rules leave no room in is not a cell to fill.
 *
 * <p>No value stands there in any row, so a row is owed for none of its classes. Left in the
 * combinations, every one of them is a combination no row can be written for — including the ones
 * that name a position beside it and have nothing to do with this one, since a row fixes every
 * position it has.
 *
 * <p>Which is what a row generated for the position beside it costs: an author is told no row can be
 * written for {@code flag = true} when one plainly can, and the reason names a collection they were
 * not asking about.
 */
class ACollectionWithNoRoomHasNoPositionInsideItTest {

    private static final String MODULE = "example.capped";

    private static final String MODEL = """
            module example.capped

            data Empty = List<Int>
                invariant none = List.length(value) <= 0
            data Box =
                { xs: Empty
                , flag: Bool
                }
            data Count = Int

            behavior only : (box: Box) -> Count
                constructs Count
            let only (box) =
                Count(List.length(List.filter(n -> n >= 5, box.xs.value)))
            """;

    private static Adequacy.Filling generated() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.diagnostics().values().stream()
                .flatMap(List::stream).toList(), "the model under test compiles");
        Adequacy.Filling only = compilation.db()
                .ask(new Adequacy.Generated(MODULE)).value().get("only");
        assertNotNull(only, "rows are asked for");
        return only;
    }

    /** The rows the position beside it is owed are written, and nothing is left unresolved. */
    @Test
    void thePositionBesideItIsStillOfferedItsRows() {
        assertEquals(List.of(), generated().composed().unresolved(),
                "no combination is one a row cannot be written for");
        assertEquals(List.of("Box { xs = Empty([]), flag = true }",
                        "Box { xs = Empty([]), flag = false }"),
                generated().composed().rows().stream()
                        .map(row -> row.inputs().get(0).text()).toList());
    }
}
