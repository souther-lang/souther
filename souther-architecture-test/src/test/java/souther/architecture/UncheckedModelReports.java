package souther.architecture;

import java.lang.classfile.ClassModel;
import java.lang.classfile.MethodModel;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
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
 * ({@link ModelWalk}): through the local variable that holds it and the variables it is copied
 * to, through a field it is written into and read out of, through the methods that make it, answer
 * it, take it, read it or ask about it, and through the ways a method can go, including the one
 * into a handler.
 *
 * <p>A read counts where the model stands as asked about on every way to it, or is asked about on
 * every way out of the method after it, so that a test can read what a model has computed before
 * anything was answered and still be held to its compiling. What was asked is not kept past what
 * changes the model: handing it new sources, or a policy, or a measure, makes it a model that was
 * not asked about. A lambda made with a model asks nothing until it is run, so making one asks
 * nothing. A look at {@code errors()} written in the test is not a look, because nothing says what
 * was done with what it showed; the tests that mean a model not to compile say so to the helper.
 *
 * <p>What is not followed is refused and not let through: a model whose origin cannot be placed is
 * one the test is not shown to have been asked about, and so is a model a method reads that nobody
 * hands it, which is what a method run by the test engine is given. A method that reads a model
 * without compiling it says so to the helper and is named in the list the check is given; no other
 * method is let say so. What is asked of the other methods is found by going round until nothing
 * changes, and that is held to a number of rounds; a check that did not settle says so and does
 * not pass.
 */
final class UncheckedModelReports {

    /** What was found: the methods refused, and how many methods read a model they asked about. */
    record Findings(Set<String> refused, int asked, Map<String, String> why) { }

    private static final int ROUNDS = 100;

    private final String helper;

    private final Set<String> exempt;

    private final Set<String> validating;

    /**
     * @param helper     the class a test goes through to ask that a model compiles
     * @param exempt     the methods, as {@link AMethod} says them, that read a model they did not
     *                   compile and say so
     * @param validating the methods of the compiler, not walked, that read what a model found and
     *                   stop unless it compiles, so that a model handed to one is asked about
     *                   when it returns
     */
    UncheckedModelReports(String helper, Set<String> exempt, Set<String> validating) {
        this.helper = helper;
        this.exempt = Set.copyOf(exempt);
        this.validating = Set.copyOf(validating);
    }

    /**
     * What {@code classes} do with the models they read, where {@code production} is the
     * compiler's own code they hand models to. What a method of either does to a model is worked
     * out from both ({@link ModelEffects}), and the methods of {@code classes} are walked.
     * The helper's own methods are not walked: they are what asks, and are held by their own tests.
     */
    Findings of(Collection<ClassModel> classes, Collection<ClassModel> production) {
        Map<String, ModelWalk> walks = new LinkedHashMap<>();
        Set<String> written = new HashSet<>();
        Map<String, Integer> captured = new HashMap<>();
        for (ClassModel each : classes) {
            if (ModelWalk.isHelper(each.thisClass().asInternalName(), helper)) {
                continue;
            }
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
        List<ClassModel> everything = new ArrayList<>(classes);
        everything.addAll(production);
        ModelWalk.World world = new ModelWalk.World(helper, Set.copyOf(walks.keySet()),
                Set.copyOf(written), Map.copyOf(captured), exempt,
                ModelEffects.of(everything), validating);
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

    private Findings findings(Map<ModelWalk, ModelWalk.Result> results) {
        Set<String> handed = new HashSet<>();
        for (ModelWalk walk : results.keySet()) {
            handed.addAll(walk.handedOn());
        }
        Set<String> refused = new TreeSet<>();
        Map<String, String> why = new TreeMap<>();
        int asked = 0;
        for (Map.Entry<ModelWalk, ModelWalk.Result> each : results.entrySet()) {
            ModelWalk walk = each.getKey();
            ModelWalk.Result result = each.getValue();
            boolean nobodyHandsItIn = result.readsParameter.stream()
                    .anyMatch(index -> !handed.contains(walk.key() + "#" + index));
            boolean theEngineHandsItIn = walk.engineRuns() && !result.readsParameter.isEmpty();
            if (result.unasked > 0 || result.lost > 0 || nobodyHandsItIn || theEngineHandsItIn) {
                String method = AMethod.of(walk.owner(), walk.method());
                refused.add(method);
                why.put(method, "unasked " + result.unasked + ", origin lost " + result.lost
                        + (nobodyHandsItIn ? ", a parameter nobody hands in" : "")
                        + (theEngineHandsItIn ? ", a parameter the engine hands in" : "")
                        + " " + result.notes.stream().limit(3).toList());
            }
            if (result.asked > 0) {
                asked++;
            }
        }
        return new Findings(refused, asked, why);
    }

    private static ModelWalk.Facts factsOf(Map<ModelWalk, ModelWalk.Result> results) {
        Map<String, ModelStanding> returns = new HashMap<>();
        Map<String, ModelStanding> storeReturns = new HashMap<>();
        Set<String> storesMadeAlone = new HashSet<>();
        Set<String> returnsParameter = new HashSet<>();
        Set<String> readsParameter = new HashSet<>();
        Set<String> readsReportParameter = new HashSet<>();
        Set<String> readsStrictParameter = new HashSet<>();
        Set<String> asksParameter = new HashSet<>();
        Set<String> mutatesParameter = new HashSet<>();
        Set<String> leavesAsked = new HashSet<>();
        Map<String, ModelStanding> fields = new HashMap<>();
        Map<String, Set<String>> fieldFlows = new HashMap<>();
        for (Map.Entry<ModelWalk, ModelWalk.Result> each : results.entrySet()) {
            String key = each.getKey().key();
            ModelWalk.Result result = each.getValue();
            if (result.returns != ModelStanding.ASKED) {
                returns.put(key, result.returns);
            }
            if (each.getKey().handsBackAStore()) {
                storeReturns.put(key, result.returnsStore);
                if (result.returnsOnlyStoresItMade) {
                    storesMadeAlone.add(key);
                }
            }
            result.returnsParameter.forEach(index -> returnsParameter.add(key + "#" + index));
            result.readsParameter.forEach(index -> readsParameter.add(key + "#" + index));
            result.readsReportParameter.forEach(index -> readsReportParameter
                    .add(key + "#" + index));
            result.readsStrictParameter.forEach(index -> readsStrictParameter
                    .add(key + "#" + index));
            result.asksParameter.forEach(index -> asksParameter.add(key + "#" + index));
            result.mutatesParameter.forEach(index -> mutatesParameter.add(key + "#" + index));
            result.exits.forEach((index, standing) -> {
                if (standing == ModelStanding.ASKED) {
                    leavesAsked.add(key + "#" + index);
                }
            });
            result.fieldWrites.forEach((field, standing) -> fields.merge(field, standing,
                    ModelStanding::join));
            result.fieldFlows.forEach((parameter, flowing) -> fieldFlows
                    .computeIfAbsent(parameter, k -> new HashSet<>()).addAll(flowing));
        }
        Set<String> changingMethods = new HashSet<>();
        mutatesParameter.forEach(each -> changingMethods.add(each.substring(0,
                each.lastIndexOf('#'))));
        return new ModelWalk.Facts(returns, returnsParameter, readsParameter,
                readsReportParameter, readsStrictParameter, asksParameter, mutatesParameter,
                leavesAsked, fields, fieldFlows, changingMethods, storeReturns, storesMadeAlone);
    }
}
