package souther.compiler;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.List;

/**
 * The obligations of a model that stay undecided on whether a row can be written for them.
 *
 * <p>Asked of the document and not of the page: the document says which question an obligation is
 * open on in a word of its schema, so this does not depend on how the page says it. Each obligation
 * open on that question is one entry, and a model whose every point has a row composed for it has
 * none.
 */
final class ObligationsNoRowCouldBeWrittenFor {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private ObligationsNoRowCouldBeWrittenFor() {
    }

    /** One entry for each obligation of {@code model} open on whether a row can be written. */
    static List<String> in(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        ACompiledModel.compiles(compilation);
        JsonNode document = JSON.readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts())));
        List<String> open = new ArrayList<>();
        for (JsonNode questions : document.findValues("undecidedAbout")) {
            for (JsonNode question : questions) {
                if (question.asString("").equals("whether_a_row_can_be_written")) {
                    open.add(question.asString());
                }
            }
        }
        return open;
    }
}
