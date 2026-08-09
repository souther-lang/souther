package souther.compiler.check;

import souther.compiler.Prelude;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.DiagnosticCode;
import souther.compiler.diag.Region;

import java.util.List;

/**
 * What a report says about a standard-library name written bare (spec §stdlib). Three readers reach
 * this — a bare name that denotes nothing, a call that reaches no callee, and a bare name written
 * where a value goes — and all three are answering the same question about the same name, so they
 * say it in one place rather than each writing the sentence out.
 *
 * <p>It is a name and not a function: the library publishes values too ({@code Map.empty}), and a
 * function's own name is a value where it is handed to a combinator rather than applied. All of
 * them are reached the same two ways, so all of them are told the same thing.
 */
final class StdlibNames {

    private StdlibNames() {}

    /**
     * The report for {@code bare} written where nothing else answers to it, or null where the
     * library publishes no such name and the caller's own report stands.
     *
     * <p>Every candidate is named, not one: a bare {@code insert} could be reaching for
     * {@code Map.insert} or {@code Set.insert}, and offering only the first would be telling the
     * reader the other does not exist. Both ways of reaching the library are offered too, because
     * both are what the language says: write the qualifier, or import the name and write it bare.
     */
    static CompileException writtenBare(String written, String bare, Region region) {
        List<String> candidates = Prelude.qualifiedCandidates(bare);
        if (candidates.isEmpty()) {
            return null;
        }
        String list = Prelude.candidateList(bare);
        return CompileException.of(Diagnostic.of(DiagnosticCode.E1025, "check.stdlib.qualified.msg")
                        .at(region).args(written, list).build());
    }
}
