package souther.compiler.check;

import souther.compiler.diag.Located;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Compilation;
import souther.compiler.source.SourceId;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A bare behavior name two import lines both claim is settled where claims are settled, and by
 * nothing else.
 *
 * <p>Two rules used to fire. The contest between the claims is settled where a scope is assembled;
 * the pass that collects borrowed signatures walked the same lines again, found the same two, and
 * refused them under a rule of its own — so an author who wrote one pair of lines was told about it
 * twice, in two vocabularies, on the same line.
 *
 * <p>The second rule is not the same rule, which is why it is still here. A behavior's name is a
 * member of the generated class, so two of them cannot share it however they arrived — and one of
 * the ways they arrive is a qualified reference, which claims no bare spelling and so is settled by
 * no contest. That case has one rule too, and it is that one.
 */
class OneContestedBehaviorNameIsSettledByOneRuleTest {

    private static final String OTHER = """
            module app.other exposing ( In, Mid, quote )
            data In = { n: Int }
            data Mid = { n: Int }
            behavior quote : (i: In) -> Mid constructs Mid
            let quote (i) = Mid { n = i.n }
            """;

    private static final String THIRD = """
            module app.third exposing ( In2, Mid, quote )
            data In2 = { n: Int }
            data Mid = { n: Int }
            behavior quote : (i: In2) -> Mid constructs Mid
            let quote (i) = Mid { n = i.n }
            """;

    /** What was said about {@code own.sou}, as the message each report carries. */
    private static List<String> saidAbout(String own) {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("other.sou", OTHER);
        byId.put("third.sou", THIRD);
        byId.put("own.sou", own);
        Compilation compilation = Compilation.ofDocuments(byId, Set.of(), ModulePath.EMPTY);
        List<String> said = new ArrayList<>();
        for (Located each : compilation.diagnostics().get(new SourceId("own.sou"))) {
            said.add(each.diagnostic().said().getClass().getSimpleName());
        }
        return said;
    }

    /** Two written lines, each bringing a behavior of one name. One fact, one report. */
    @Test
    void twoWrittenLinesAreOneReport() {
        assertEquals(List.of("TheNameIsImportedFromTwoModules"), saidAbout("""
                module app.own exposing ( Out )
                import app.other ( quote )
                import app.third ( quote )
                data Out = { n: Int }
                """),
                "the contest between the claims settles it, and nothing settles it again");
    }

    /**
     * A written line and a qualified reference, which no contest settles.
     *
     * <p>The reference names its module, so what it denotes was never in doubt and the scope says
     * nothing. What the two cannot both have is the member name in the generated class, and that is
     * this rule.
     */
    @Test
    void aQualifiedReferenceBesideAWrittenLineIsStillRefused() {
        assertEquals(List.of("ABehaviorIsNamedFromTwoModules", "ImportedButNeverUsedUnderThisName"),
                saidAbout("""
                        module app.own exposing ( Out, flow : Out )
                        import app.other ( quote, In )
                        data Out = { n: Int }
                        behavior plus : (m: app.other.Mid) -> Out constructs Out
                        let plus (m) = Out { n = m.n + 1 }
                        behavior flow = quote >-> plus
                        behavior other = app.third.quote >-> plus
                        """),
                "no claim was made on the bare spelling, so this is the one rule that sees it");
    }
}
