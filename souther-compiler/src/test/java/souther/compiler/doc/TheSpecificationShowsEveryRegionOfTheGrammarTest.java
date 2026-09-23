package souther.compiler.doc;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.util.Set;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The specification shows the grammar by including it, region by region, and the specification
 * {@code souther doc} answers from reads with those includes resolved.
 *
 * <p>The grammar is written once, in {@code syntax/grammar.ebnf}, and each construct's section
 * includes the region that holds its productions. A region no section includes is grammar a reader
 * of the specification never sees, and a section including a region the grammar does not have is
 * shown nothing — both are the specification and the grammar disagreeing about what is written
 * where, which is what writing a form in one place was for.
 */
class TheSpecificationShowsEveryRegionOfTheGrammarTest {

    private static final Pattern REGION = Pattern.compile("tag::([a-z0-9-]+)\\[]");
    private static final Pattern INCLUDED =
            Pattern.compile("(?m)^include::syntax/grammar\\.ebnf\\[tag=([a-z0-9-]+)[],]");

    @Test
    void everyRegionIsIncludedAndEveryIncludeIsARegion() throws IOException {
        assertEquals(found(REGION, bundled("/META-INF/souther/syntax/grammar.ebnf")),
                found(INCLUDED, bundled("/META-INF/souther/specification.adoc")));
    }

    @Test
    void aSectionReadsAsTheGrammarItIncludesAndNotAsTheDirective() {
        SpecDocument spec = SpecDocument.bundled();
        String match = spec.section("match").body();
        assertTrue(match.contains("@node match-expression"), match);
        String grammar = spec.section("grammar").body();
        assertTrue(grammar.contains("Match-arm column rule"), grammar);
        for (SpecDocument.Section each : spec.sections()) {
            assertFalse(each.body().contains("include::"), each.anchor() + " still writes an include");
        }
    }

    private static Set<String> found(Pattern pattern, String text) {
        Set<String> out = new TreeSet<>();
        Matcher matcher = pattern.matcher(text);
        while (matcher.find()) {
            out.add(matcher.group(1));
        }
        return out;
    }

    private static String bundled(String resource) throws IOException {
        try (InputStream in = TheSpecificationShowsEveryRegionOfTheGrammarTest.class
                .getResourceAsStream(resource)) {
            assertNotNull(in, "not bundled: " + resource);
            return new String(in.readAllBytes(), StandardCharsets.UTF_8);
        }
    }
}
