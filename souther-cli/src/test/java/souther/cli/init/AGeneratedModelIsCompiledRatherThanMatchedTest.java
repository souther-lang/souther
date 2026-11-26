package souther.cli.init;

import org.junit.jupiter.api.Test;
import souther.compiler.ACompiledModel;
import souther.compiler.Compiler;
import souther.compiler.diag.Located;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What {@code init} writes is put through the compiler, not compared with a string.
 *
 * <p>A template held against an expected text goes on passing after the language moves under it: the
 * text and the template are edited together, and the thing neither of them is held against is
 * whether the result still compiles. What a reader gets from this command is a project that builds,
 * so that is what is asked here.
 */
class AGeneratedModelIsCompiledRatherThanMatchedTest {

    private static final Project MAVEN = new Project(new Coordinate("com.example", "hello"),
            "com.example.hello", Model.FULL, BuildSystem.MAVEN, "9.9.9");

    private static Project at(Model model) {
        return new Project(MAVEN.coordinate(), MAVEN.moduleName(), model, MAVEN.build(),
                MAVEN.southerVersion());
    }

    /**
     * The levels short of {@code full} compile, including the one that is a module header and nothing
     * else. The {@code full} one is compiled below, where its rows are read as well.
     */
    @Test
    void everyModelShortOfTheFullOneCompiles() {
        for (Model model : Model.values()) {
            if (model == Model.FULL) {
                continue;
            }
            List<Located> warnings = new ArrayList<>();
            Compilation compiled = Compiler.compiledModules(texts(model), ModulePath.EMPTY,
                    warnings, Adequacy.Asked.NOTHING);
            assertTrue(compiled.classes().size() > 0 || model == Model.NONE,
                    model + " compiled to no classes at all");
            assertEquals(List.of(), warnings.stream().map(Object::toString).toList(),
                    model + " compiles with a warning");
        }
    }

    private static List<String> texts(Model model) {
        return Templates.sourcesOf(at(model)).stream()
                .filter(file -> file.path().endsWith(".sou"))
                .map(Templates.File::content)
                .toList();
    }

    /**
     * The {@code full} model compiles without a warning, and the rows it comes with leave nothing
     * owed.
     *
     * <p>The point of shipping rows in a template is that {@code souther examples} answers on the
     * first run. A template whose own report names a gap teaches the reader that the report is
     * something to ignore.
     *
     * <p>Asked of the gaps rather than of the verdict. Two of this body's three rules are ones this
     * compiler could not settle — a row it composed for one took another rule of the same body — so
     * the verdict is open on that, which is this compiler's shortfall and not a row the reader is
     * missing.
     */
    @Test
    void theRowsTheFullModelComesWithLeaveNothingOwed() {
        List<Located> warnings = new ArrayList<>();
        Compilation compiled = ACompiledModel.compiles(Compiler.analyzedModules(texts(Model.FULL),
                ModulePath.EMPTY, warnings, Adequacy.Asked.fullReport()));
        AdequacyReport report = AdequacyReport.of(compiled);

        assertTrue(compiled.classes().size() > 0, "full compiled to no classes at all");
        assertEquals(List.of(), warnings.stream().map(Object::toString).toList(),
                "full compiles with a warning");

        assertEquals(List.of(), report.adequacyGaps().stream()
                        .map(each -> each.about().toString()).toList(),
                () -> "the rows shipped with `--model full` leave something owed:\n"
                        + report.humanInEnglish(souther.compiler.diag.SourceRendering.namedByIdentity(
                                compiled.texts())));
    }
}
