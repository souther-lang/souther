package souther.architecture;

import java.lang.classfile.ClassModel;
import java.lang.classfile.MethodModel;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

/**
 * The methods of some test classes that read the report of a model without the test having been
 * held to that model compiling.
 *
 * <p>A model that does not compile is said nothing of, so a report of it is empty and a test that
 * asks that nothing of some kind is said passes on it. What is wanted is that a test cannot pass
 * without the model it read having been handed to the helper, which stops the test on an error or
 * says which errors the model is meant to be refused with. That is a fact about one value, and
 * about every way a method can run, so each model is followed through the method that makes it
 * ({@link ModelWalk}): through the local variable that holds it, through a field it is written into
 * and read out of, through the methods that make it, answer it, take it, read it or ask about it,
 * and through the ways a method can go, including the one into a handler.
 *
 * <p>A read counts where the model stands as asked about on every way to it, or is asked about on
 * every way out of the method after it, so that a test can read what a model has computed before
 * anything was answered and still be held to its compiling. A look at {@code errors()} written in
 * the test is not a look, because nothing says what was done with what it showed; the tests that
 * mean a model not to compile say so to the helper.
 *
 * <p>What is not followed is refused and not let through: a model whose origin cannot be placed is
 * one the test is not shown to have been asked about. What is asked of the other methods is found
 * by going round until nothing changes, and that is held to a number of rounds; a check that did
 * not settle says so and does not pass.
 */
final class UncheckedModelReports {

    /** What was found: the methods refused, and how many methods read a model they asked about. */
    record Findings(Set<String> refused, int asked) { }

    private static final int ROUNDS = 100;

    private final String helper;

    /** @param helper the class a test goes through to ask that a model compiles */
    UncheckedModelReports(String helper) {
        this.helper = helper;
    }

    /** What {@code classes} do with the models they read. */
    Findings of(Collection<ClassModel> classes) {
        Map<String, ModelWalk> walks = new LinkedHashMap<>();
        Set<String> written = new HashSet<>();
        Map<String, Integer> captured = new HashMap<>();
        for (ClassModel each : classes) {
            for (MethodModel method : each.methods()) {
                if (method.code().isPresent()) {
                    ModelWalk walk = new ModelWalk(each, method, helper);
                    if (walk.relevant()) {
                        walks.put(walk.key(), walk);
                        written.addAll(walk.fieldsWritten());
                        walk.capturedByLambdas().forEach((impl, count) -> captured.merge(impl,
                                count, Math::max));
                    }
                }
            }
        }
        ModelWalk.World world = new ModelWalk.World(helper, Set.copyOf(walks.keySet()),
                Set.copyOf(written), Map.copyOf(captured));
        ModelWalk.Facts facts = ModelWalk.Facts.NONE;
        Map<ModelWalk, ModelWalk.Result> results = new LinkedHashMap<>();
        for (int round = 0; round < ROUNDS; round++) {
            results.clear();
            for (ModelWalk walk : walks.values()) {
                results.put(walk, walk.run(facts, world));
            }
            ModelWalk.Facts found = factsOf(results);
            if (found.equals(facts)) {
                return findings(results);
            }
            facts = found;
        }
        throw new IllegalStateException("what the methods do with a model did not settle in "
                + ROUNDS + " rounds, so nothing can be said of the reads");
    }

    private static Findings findings(Map<ModelWalk, ModelWalk.Result> results) {
        Set<String> refused = new TreeSet<>();
        int asked = 0;
        for (Map.Entry<ModelWalk, ModelWalk.Result> each : results.entrySet()) {
            ModelWalk.Result result = each.getValue();
            if (result.unasked > 0 || result.lost > 0) {
                refused.add(AMethod.of(each.getKey().owner(), each.getKey().method()));
            }
            if (result.asked > 0) {
                asked++;
            }
        }
        return new Findings(refused, asked);
    }

    private static ModelWalk.Facts factsOf(Map<ModelWalk, ModelWalk.Result> results) {
        Map<String, ModelStanding> returns = new HashMap<>();
        Set<String> returnsParameter = new HashSet<>();
        Set<String> readsParameter = new HashSet<>();
        Set<String> asksParameter = new HashSet<>();
        Map<String, ModelStanding> fields = new HashMap<>();
        Map<String, Set<String>> fieldFlows = new HashMap<>();
        for (Map.Entry<ModelWalk, ModelWalk.Result> each : results.entrySet()) {
            String key = each.getKey().key();
            ModelWalk.Result result = each.getValue();
            if (result.returns != ModelStanding.ASKED) {
                returns.put(key, result.returns);
            }
            result.returnsParameter.forEach(index -> returnsParameter.add(key + "#" + index));
            result.readsParameter.forEach(index -> readsParameter.add(key + "#" + index));
            result.asksParameter.forEach(index -> asksParameter.add(key + "#" + index));
            result.fieldWrites.forEach((field, standing) -> fields.merge(field, standing,
                    ModelStanding::join));
            result.fieldFlows.forEach((parameter, flowing) -> fieldFlows
                    .computeIfAbsent(parameter, k -> new HashSet<>()).addAll(flowing));
        }
        return new ModelWalk.Facts(returns, returnsParameter, readsParameter, asksParameter,
                fields, fieldFlows);
    }
}
