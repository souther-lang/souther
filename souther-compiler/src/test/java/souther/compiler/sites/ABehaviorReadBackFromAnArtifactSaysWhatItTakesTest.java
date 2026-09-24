package souther.compiler.sites;

import souther.compiler.Compiler;
import souther.compiler.cst.SourceLayout;
import souther.compiler.diag.SourcePos;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Compilation;
import souther.compiler.types.Type;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What a behavior takes is answered for one read back from an artifact as it is for one written
 * here.
 *
 * <p>A jar carries the declaration and not the witness: the module travels as the source its author
 * wrote, and the importing compilation admits it with the same walk. So the reading that says what a
 * name takes asks the module that declares it and never learns which of the two it is — the answer
 * exists because this compilation built it, whichever tree it was built from.
 *
 * <p>This is the boundary that would fail quietly. A signature serialised into the artifact would be
 * a second representation of what the declaration already says, and a reading that special-cased a
 * borrowed behavior would answer with less about one — nothing at all, most likely, which reads as a
 * name that reaches nothing rather than as a gap.
 *
 * <p>Asked over a stage of a composition, because a stage is a name that reaches a behavior. A body
 * calls what its {@code depends on} clause handed it, which is a parameter holding a function and
 * not the declaration, and the reading says so by answering nothing there.
 */
class ABehaviorReadBackFromAnArtifactSaysWhatItTakesTest {

    private static final String LIBRARY = """
            module shared.money exposing ( Amount, tally, tallied : Amount )

            data Amount = Int

            behavior tally : (amount: Amount) -> Amount

            behavior tallied = tally >-> tally
            """;

    private static final String CONSUMER = """
            module app.order
            import shared.money ( tally, tallied )

            behavior twice = tally >-> tally

            behavior again = tallied >-> tally
            """;

    /** The consumer compiled once against the published library, with every question answered, and
     *  read by each case. The readings below ask what is already answered and change nothing. */
    private static final Compilation COMPILATION = compiled();

    private static Compilation compiled() {
        ModulePath published = ModulePath.of(Compiler.compile(LIBRARY));
        Compilation compilation = Compilation.ofDocuments(
                Map.of("a.sou", CONSUMER), Set.of(), published);
        compilation.answerEverything();
        return compilation;
    }

    @Test
    void aBorrowedBehaviorNamesItsParametersAndTheirTypes() {
        assertEquals(List.of(), COMPILATION.db().allReports().stream()
                .map(each -> each.report().diagnostic().said().getClass().getSimpleName()).toList(),
                "the model under test compiles");
        CalledBehavior called = SemanticSnapshot.of(COMPILATION.db(), "app.order").orElseThrow()
                .calledAt(over(COMPILATION, "behavior twice =", "tally")).orElseThrow();

        assertEquals("tally", called.name());
        assertEquals(List.of("amount"), namesOf(called));
        assertEquals(List.of("Amount"), typesOf(called));
    }

    /** A composition read back from an artifact names no parameters, as one written here does not:
     *  what the artifact carries of its signature is what its stages compute, and the names written
     *  there to carry it are nobody's. */
    @Test
    void aBorrowedCompositionNamesNoParameters() {
        assertEquals(Optional.empty(), SemanticSnapshot.of(COMPILATION.db(), "app.order")
                .orElseThrow().calledAt(over(COMPILATION, "behavior again =", "tallied")));
    }

    /**
     * Where {@code word} is written after the consumer's {@code line}, in the file this compilation
     * read it from.
     *
     * <p>Read off the text as it is laid out, because that is what a place is made from. Counted
     * into a line and a column instead, the numbers would be type-correct and name whatever token
     * happens to be counted that far along.
     */
    private static SourcePos over(Compilation compilation, String line, String word) {
        int at = CONSUMER.indexOf(line);
        if (at < 0) {
            throw new AssertionError("the source under test no longer writes " + line);
        }
        return SourceLayout.of(CONSUMER, compilation.sourceIds().get(0))
                .placeAt(CONSUMER.indexOf(word, at));
    }

    private static List<String> namesOf(CalledBehavior called) {
        List<String> names = new ArrayList<>();
        called.takes().forEach(each -> names.add(each.name()));
        return names;
    }

    private static List<String> typesOf(CalledBehavior called) {
        List<String> types = new ArrayList<>();
        called.takes().forEach(each -> types.add(Type.show(each.type().type())));
        return types;
    }
}
