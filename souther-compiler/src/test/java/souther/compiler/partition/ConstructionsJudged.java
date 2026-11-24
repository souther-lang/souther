package souther.compiler.partition;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Compilation;

import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

/**
 * What is judged of each construction of one behavior ({@link StopsOfABody}), by the line the
 * construction is written on: the kind of judgement it was given.
 *
 * <p>For a test that says a construction stops no run. The report says nothing of one, and says
 * the same of one never asked about, so the judgement is what tells the two apart.
 */
final class ConstructionsJudged {

    private ConstructionsJudged() {}

    /** The kinds of judgement each construction of {@code behavior} in {@code compilation}'s one
     *  module was given, by its line. */
    static Map<Integer, Set<String>> of(Compilation compilation, String behavior) {
        SourceRendering rendering = SourceRendering.namedByIdentity(compilation.texts());
        Map<Integer, Set<String>> out = new TreeMap<>();
        for (StopsOfABody.AtAStep each : SitesJudged.steps(compilation, behavior)) {
            each.construction().ifPresent(judged -> out.computeIfAbsent(
                    rendering.layouts().resolve(judged.made().pos()).line(),
                    _ -> new TreeSet<>()).add(judged.getClass().getSimpleName()));
        }
        return out;
    }
}
