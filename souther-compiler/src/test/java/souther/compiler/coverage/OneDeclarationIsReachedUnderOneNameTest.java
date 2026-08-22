package souther.compiler.coverage;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * Which declaration a fork was written in and which one a copy is of are said the same way.
 *
 * <p>The reading of the declarations walks what a body can reach and keys what it finds by the name
 * it reaches it under; the expansion looks its callee up in that same table, under the name the call
 * resolved to. So the two say which declaration alike, and a copy can be matched against the
 * declaration whose parameters were named.
 *
 * <p>Measured across a module boundary, where the two could most easily part: a helper of another
 * module is reached under a name that module's own body would not use for it. Two calls of it with
 * two rules are two obligations, which is only sayable if the names met.
 */
class OneDeclarationIsReachedUnderOneNameTest {

    private static final String LIB = """
            module ex.lib exposing ( choose, Verdict, Yes, No )

            data Yes
            data No
            data Verdict = Yes | No

            let choose (p: (Int) -> Bool, x: Int): Verdict =
                if p(x) then Yes else No
            """;

    private static final String APP = """
            module ex.app

            import ex.lib ( choose, Yes )

            data Count = Int

            behavior twice : (a: Int, b: Int) -> Count
                constructs Count
            let twice (a, b) =
                Count((if choose(n -> n < 18, a) == Yes then 1 else 0)
                    + (if choose(m -> 18 <= m, b) == Yes then 1 else 0))

            example twice
                | "under and over" : (1, 1) -> Count(1)
            """;

    @Test
    void aHelperOfAnotherModuleIsOneObligationPerRuleHandedIn() {
        Compilation compilation = Compilation.ofSources(List.of(LIB, APP),
                souther.compiler.meta.ModulePath.EMPTY);
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        Adequacy.BranchEvidence twice = compilation.db()
                .ask(new Adequacy.BranchCoverage("ex.app")).value().get("twice");
        assertNotNull(twice, "the models under test compile");

        assertEquals(8, twice.obligations(),
                "the other module's fork is one obligation per rule handed to it, beside the two"
                        + " written here");
        assertEquals(List.of(), twice.countedTogether(),
                () -> "and which copy each is was said: " + twice.countedTogether());
    }
}
