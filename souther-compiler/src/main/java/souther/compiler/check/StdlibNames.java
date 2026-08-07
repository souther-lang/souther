package souther.compiler.check;

import souther.compiler.Prelude;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.Region;

import java.util.List;

/**
 * What a report says about a standard-library name written bare (spec §stdlib). Two passes reach
 * this — resolution, where a bare name denotes nothing, and elaboration, where a call reaches no
 * callee — and both are answering the same question about the same name, so they say it in one
 * place rather than each writing the sentence out.
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
        return CompileException.of(
                Diagnostic.of(null, "check.stdlib.qualified.msg").title("check.unknown.title")
                        .at(region).args(written, list).build(),
                "`" + written + "` is a standard-library function. Write it qualified (" + list
                        + ") or import the name you mean (spec §stdlib).");
    }
}
