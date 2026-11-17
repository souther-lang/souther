package souther.bench;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.diag.SourceRendering;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;
import souther.test.ClosedWorldContract;
import souther.test.Nightly;

import java.util.List;
import java.util.stream.IntStream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * That the count of what two lookups matched, in the crm corpus, is read at every place it names.
 *
 * <p>The count is over the accounts an address's domain matches and the contacts its address
 * matches, each made distinct by id, after a guard on an address a contact point may not have.
 * Its comparison relates a piece of the lowercased address to the domain of an account, and one
 * address to another, in every case of the contact point. It is the shape the model is written in,
 * and a smaller one that keeps the relations does not keep the length of the way to them: a
 * sum with a case that has no address, two lookups through a sum, and ids made distinct.
 *
 * <p>Asked once a night, for the reason {@link CorpusTest} is: the claim is of the corpus, and
 * measuring a model of that size costs more than a change waits on. The set is the places the
 * comparison names, which the report declares, and the claim is that none is left as a position
 * the report cannot say anything of: each is said to divide the position or to leave it
 * undivided. Each is named here, with the case it is a value under, so that a place the report
 * stops naming is found as well as one it leaves unread.
 */
@ClosedWorldContract
@Nightly
class TheCountOverWhatTwoLookupsMatchIsReadAtEveryPlaceItNamesTest {

    private static final String THE_COUNT =
            "guard List.length(matchedAccounts) + List.length(matchedContacts) >= 1";

    private static final List<String> PLACES = List.of(
            "accounts[*].domain@Some",
            "lead.reach@EmailOnly.email",
            "lead.reach@EmailAndPhone.email",
            "contacts[*].reach@EmailOnly.email",
            "contacts[*].reach@EmailAndPhone.email");

    @Test
    void everyPlaceTheCountNamesIsRead() {
        Corpus crm = Corpus.load("crm");
        int line = lineOfTheCount(crm);
        Compilation compilation = Compilation.ofSources(crm.sources(), ModulePath.EMPTY);
        compilation.measure(Adequacy.Asked.fullReport());
        ACompiledModel.compiles(compilation);
        String page = AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()));
        String comparison = "comparison@" + line + ":";

        List<String> ofTheCount = page.lines().filter(each -> each.contains(comparison)).toList();
        assertTrue(ofTheCount.size() >= PLACES.size(), "the report says nothing of the count");
        assertEquals(List.of(), ofTheCount.stream().filter(each -> each.contains("not read:")
                || each.contains("not accounted for:")).toList());
        assertEquals(List.of(), PLACES.stream().filter(place -> ofTheCount.stream().noneMatch(
                each -> each.contains("`" + place + "`")
                        || each.contains(place + " is divided by"))).toList(),
                "places the report names nothing of");
    }

    /** The line, counting from one, of the count in the source that holds it. */
    private static int lineOfTheCount(Corpus crm) {
        for (String source : crm.sources()) {
            List<String> lines = source.lines().toList();
            int at = IntStream.range(0, lines.size())
                    .filter(each -> lines.get(each).contains(THE_COUNT)).findFirst().orElse(-1);
            if (at >= 0) {
                return at + 1;
            }
        }
        throw new IllegalStateException("the corpus no longer holds the count");
    }
}
