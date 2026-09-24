package souther.compiler.core;

import souther.compiler.conformance.ConformanceCorpus;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.types.BinOp;
import souther.compiler.types.Type;
import souther.test.ClosedWorldContract;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.function.Consumer;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Every tree the checker hands out of checking has exact typed slots: where a node says what type a
 * slot of it takes its value at, the value in the slot is of that type.
 *
 * <p>A fork answers what its branches join at, and each branch is of that type; a list holds its
 * elements at the type it is a list of; a binding holds its value at the type it is in force at and
 * answers what its body answers; an optional holds what it holds at the type it is an optional of;
 * {@code ++} over lists takes both sides at the list it answers; a kernel's application takes each
 * argument at what it settled it takes it as. Where a value is narrower than the slot, what stands
 * there is the {@link Core.Widen} saying it may stand as that type, so none of these is a question a
 * reader of the tree has to answer again.
 *
 * <p>A block is not among them. What it answers is its body's type, read off the body, so there is
 * no second type for the body to disagree with.
 *
 * <p>Of the trees checking hands out, and not of every {@code Core} anything builds. A pass after
 * checking rewrites the tree it is handed, and an analysis may build a node of its own to read, and
 * neither is held here.
 *
 * <p>What a call to a declaration takes, and what a construction's fields take, are said by the
 * declarations and not by the node, so they are held where the declaration is read ({@link
 * AValueStandsAsWhatItsPositionTakesItAsTest}) rather than here. A kernel's signature is declared
 * with type variables each application settles, so what one application takes is said by the call.
 * The trees read here keep the language's operations standing as themselves, so a kernel applied to
 * arguments is met in the body handed on to be emitted, which {@link
 * EveryTreeTheBackendIsHandedIsTypedTest} asks this of.
 */
@ClosedWorldContract
class EverySlotHoldsWhatItsNodeTakesItAsTest {

    @Test
    void everySlotAWrittenTypeDecidesHoldsAValueOfThatType() {
        List<Core> trees = trees();
        assertFalse(trees.isEmpty(), "no tree was read, so this holds of nothing");
        List<String> found = new ArrayList<>();
        for (Core tree : trees) {
            each(tree, node -> found.addAll(disagreements(node)));
        }
        assertEquals(List.of(), found,
                "a slot holding a value of a type other than the one its node takes it at, with no"
                        + " Widen saying the value may stand as that type");
    }

    /**
     * And that the corpus writes branches and arms narrower than what they join at, so the rule
     * above is asked of a Widen where it matters and not only of values already exact. The other
     * positions it reads are written by the models beside {@link
     * AValueStandsAsWhatItsPositionTakesItAsTest}, which the corpus has no reason to write.
     */
    @Test
    void theCorpusWidensBranchesAndArms() {
        Set<String> widenedUnder = new TreeSet<>();
        for (Core tree : trees()) {
            each(tree, node -> Core.forEachChild(node, child -> {
                if (child instanceof Core.Widen) {
                    widenedUnder.add(node.getClass().getSimpleName());
                }
            }));
        }
        assertTrue(widenedUnder.containsAll(Set.of("If", "Match")),
                () -> "the corpus widens under " + widenedUnder
                        + ", which does not include both a branch and an arm");
    }

    /**
     * And that the rule reads what it says it reads: a branch with what it stands as set aside is a
     * disagreement.
     */
    @Test
    void aBranchWithItsStandingSetAsideIsADisagreement() {
        Core.If widened = null;
        for (Core tree : trees()) {
            List<Core.If> forks = new ArrayList<>();
            each(tree, node -> {
                if (node instanceof Core.If fork && fork.then() instanceof Core.Widen) {
                    forks.add(fork);
                }
            });
            if (!forks.isEmpty()) {
                widened = forks.getFirst();
                break;
            }
        }
        if (widened == null) {
            throw new AssertionError("no branch in the corpus is widened, so nothing here holds"
                    + " the rule to what it reads");
        }
        Core.If bare = new Core.If(widened.cond(), Core.withoutStanding(widened.then()),
                widened.els(), widened.place(), widened.type(), widened.pos());
        assertEquals(1, disagreements(bare).size(),
                "the branch, once it no longer says what it stands as");
    }

    /** What {@code node} says of a slot's type that the value in the slot does not have. */
    static List<String> disagreements(Core node) {
        List<String> out = new ArrayList<>();
        switch (node) {
            case Core.If fork -> {
                expect(out, fork, "then", fork.type(), fork.then());
                expect(out, fork, "else", fork.type(), fork.els());
            }
            case Core.IfConstructed attempt -> {
                expect(out, attempt, "then", attempt.type(), attempt.then());
                attempt.els().forEach(arm -> expect(out, attempt, "else", attempt.type(),
                        arm.body()));
            }
            case Core.Match match -> match.cases().forEach(arm ->
                    expect(out, match, "arm", match.type(), arm.body()));
            case Core.ListLit list when list.type() instanceof Type.ListOf of ->
                    list.elements().forEach(each -> expect(out, list, "element", of.element(), each));
            case Core.LetIn let -> {
                expect(out, let, "value", let.bindType(), let.value());
                expect(out, let, "body", let.type(), let.body());
            }
            case Core.OptionSome some when some.type() instanceof Type.OptionOf of ->
                    expect(out, some, "value", of.element(), some.value());
            case Core.Binary joined when joined.op() == BinOp.CONCAT
                    && joined.type() instanceof Type.ListOf -> {
                expect(out, joined, "left", joined.type(), joined.left());
                expect(out, joined, "right", joined.type(), joined.right());
            }
            case Core.Call call when call.settlement()
                    instanceof Core.CallSettlement.AtKernel(List<Type> takes, _) -> {
                if (takes.size() != call.args().size()) {
                    out.add("Call at " + call.pos() + ": `" + call.name() + "` takes "
                            + takes.size() + " argument(s) and holds " + call.args().size());
                } else {
                    for (int i = 0; i < takes.size(); i++) {
                        expect(out, call, "argument " + (i + 1) + " of `" + call.name() + "`",
                                takes.get(i), call.args().get(i));
                    }
                }
            }
            default -> { }
        }
        return out;
    }

    private static void expect(List<String> out, Core node, String slot, Type takes, Core value) {
        if (value != null && !takes.equals(value.type())) {
            out.add(node.getClass().getSimpleName() + " at " + node.pos() + ": its " + slot
                    + " is taken as " + Type.show(takes) + " and holds "
                    + Type.show(value.type()));
        }
    }

    private static void each(Core e, Consumer<Core> f) {
        if (e == null) {
            return;
        }
        f.accept(e);
        Core.forEachChild(e, child -> each(child, f));
    }

    private static List<Core> trees;

    /**
     * Every tree the checker builds for every corpus, as checking built it: what an analysis of
     * each body reads, and the template of each value it builds.
     *
     * <p>Not the body a check hands on to be emitted. That one has been through the rewrite that
     * turns a fold growing a collection into a build ({@link GrowingFold}), which is a pass after
     * checking and not held here; {@link EveryTreeTheBackendIsHandedIsTypedTest} holds that one.
     */
    private static List<Core> trees() {
        if (trees != null) {
            return trees;
        }
        List<Core> out = new ArrayList<>();
        for (ConformanceCorpus corpus : ConformanceCorpus.all()) {
            Map<String, String> byId = new LinkedHashMap<>();
            for (int i = 0; i < corpus.sources().size(); i++) {
                byId.put(corpus.files().get(i), corpus.sources().get(i));
            }
            Compilation c = Compilation.ofDocuments(byId, Set.of(), ModulePath.EMPTY);
            c.answerEverything();
            for (String module : c.modules()) {
                Set<String> names = c.declaredBehaviors(module);
                if (names == null) {
                    continue;
                }
                for (String behavior : new TreeSet<>(names)) {
                    Bodies.CheckedBody checked =
                            c.db().ask(new Bodies.CheckedBehavior(module, behavior)).value();
                    if (checked != null && checked.analysis() != null) {
                        out.add(checked.analysis().core());
                        out.addAll(checked.analysis().templatesAfterTheirBuilders());
                    }
                }
            }
        }
        trees = List.copyOf(out);
        return trees;
    }
}
