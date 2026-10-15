package souther.compiler.coverage;

import souther.compiler.core.Core;
import souther.compiler.types.ModelOccurrence;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Where the tree that runs records the answer of each application of one of the language's
 * operations the model states, by the construct of the model the application is.
 *
 * <p>The applications' half of what {@link ComparisonEmissionIndex} is for comparisons. A rule is
 * read off the tree the operations stand in and names an application by the construct of the
 * model; a run is recorded in the tree they are copied into, where a helper the application is
 * written in is copied once per call — so one construct is answered at as many places as the body
 * holds copies of it, and a run through any of them answered the application the rule names.
 *
 * <p>Read off the nodes of one body and the values it calls, and nothing else. What the plan holds
 * is every body of the module, and a rule of one behavior is not taken by a run answering at a
 * place of another.
 */
public final class AnswerEmissionIndex {

    private final Map<ModelOccurrence, List<CoverageSites.AnswerSite>> emitted;

    private AnswerEmissionIndex(Map<ModelOccurrence, List<CoverageSites.AnswerSite>> emitted) {
        this.emitted = emitted;
    }

    /** The places {@code body} and the values it calls answer at, under {@code plan}. */
    public static AnswerEmissionIndex ofBody(Core body, CoverageSites.Plan plan) {
        Map<ModelOccurrence, Set<CoverageSites.AnswerSite>> found = new LinkedHashMap<>();
        walk(body, plan, found);
        for (Core method : plan.methods().calledFrom(body)) {
            walk(method, plan, found);
        }
        Map<ModelOccurrence, List<CoverageSites.AnswerSite>> out = new LinkedHashMap<>();
        found.forEach((stated, sites) -> out.put(stated, List.copyOf(sites)));
        return new AnswerEmissionIndex(Map.copyOf(out));
    }

    private static void walk(Core e, CoverageSites.Plan plan,
                             Map<ModelOccurrence, Set<CoverageSites.AnswerSite>> found) {
        CoverageSites.AnswerSite answer = plan.answersByNode().get(e);
        if (answer != null) {
            // The plan numbers only an application the model states, so the construct is there to
            // be read; one it is not there for is a plan this index was not made from.
            ModelOccurrence stated = ModelOccurrence.statedAt(answer.application())
                    .orElseThrow(() -> new IllegalStateException("the plan records the answer of "
                            + answer.application() + ", which the model states nothing at"));
            found.computeIfAbsent(stated, _ -> new LinkedHashSet<>()).add(answer);
        }
        Core.forEachChild(e, child -> walk(child, plan, found));
    }

    /** Where a run answering {@code application} is recorded, one entry per copy of it. */
    public List<CoverageSites.AnswerSite> madeFor(ModelOccurrence application) {
        return emitted.getOrDefault(application, List.of());
    }
}
