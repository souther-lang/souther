package souther.compiler.report;

import souther.compiler.diag.Severity;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A model written to reach one arm of {@link ReaderDisposition}, measured and handed over.
 *
 * <p>The one way a witness here gets a report, because reaching the arm is not what makes a model
 * a witness. An entry survives whatever failed around it, so a model that stopped compiling goes
 * on producing the same uncertainty — the witness stays green while witnessing nothing anybody
 * could write. That is not hypothetical: a reduction over the corpora whose oracle was only the arm
 * kept a source that named a behavior it had already deleted.
 *
 * <p><b>Which is not the same as demanding a model nothing is refused about.</b> A body no
 * elaboration could be made of is refused, and a measure going without what that body's rows took
 * is exactly what one of these arms is for — so a witness for it is a model this compiler says no
 * to, and a rule against that would make the arm unwitnessable. The corpus says the same: the model
 * this shape was taken from is carried with its refusal on purpose.
 *
 * <p>So a witness declares what its model is refused about and nothing else is allowed. An error
 * the witness did not ask for is the case above — something broke that the witness is not about —
 * and it fails here rather than passing quietly.
 */
final class WrittenWitness {

    private WrittenWitness() {
    }

    /** The report of a model nothing is refused about. */
    static AdequacyReport reportOf(String... sources) {
        return refusedOnly(List.of(), sources);
    }

    /**
     * The report of a model refused about these and nothing else.
     *
     * <p>Counted and not a set of the words. A second refusal carrying a code the witness already
     * named is a second thing wrong with the model, and asked as a set it reads as the one the
     * witness asked for.
     *
     * @param codes the diagnostic codes this witness is written to provoke, one entry per refusal
     *              expected, as a document spells them
     */
    static AdequacyReport refusedOnly(List<String> codes, String... sources) {
        Compilation compilation = Compilation.ofSources(List.of(sources), ModulePath.EMPTY);
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();

        List<String> refused = compilation.diagnostics().values().stream()
                .flatMap(List::stream)
                .filter(each -> each.diagnostic().severity() == Severity.ERROR)
                .map(each -> each.diagnostic().code().toString())
                .sorted()
                .toList();

        assertEquals(codes.stream().sorted().toList(), refused,
                "a witness says what its model is refused about, and this one is refused about"
                        + " something else");
        return AdequacyReport.of(compilation);
    }
}
