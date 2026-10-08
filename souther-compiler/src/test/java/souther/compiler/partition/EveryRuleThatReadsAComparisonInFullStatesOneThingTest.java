package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.BooleanMeaning;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.StatedComparison;
import souther.compiler.core.Core;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.meaning.Derivation;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Relation;
import souther.compiler.meaning.WhyUnread;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.semantics.AnswerAspect;
import souther.compiler.types.ValueName;

import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A comparison more than one rule takes is read by all of them, and they state one thing.
 *
 * <p>A size compared with nought is both whether a container holds anything and a cut on the size,
 * and the reading tries both ({@link RuleChoice}). That is only sound where the two agree, so
 * every rule that reads one of these comparisons in full is asked on its own and its proposition
 * evaluated at every size up to a few: which rule was tried first then decides nothing a reader of
 * the proposition can tell. And where the first rule leaves a part unread, the parts a rule tried
 * after it met are no parts of what is stated.
 */
class EveryRuleThatReadsAComparisonInFullStatesOneThingTest {

    private static final String INPUT = """
            data Box = { xs: List<Int>, tags: Set<String>, m: Map<String, Int> }
            """;

    private static final List<String> SIZES_AGAINST_NOUGHT = List.of(
            "List.length(b.xs) > 0", "List.length(b.xs) >= 1", "List.length(b.xs) /= 0",
            "List.length(b.xs) == 0", "List.length(b.xs) < 1", "List.length(b.xs) <= 0",
            "0 < List.length(b.xs)", "1 <= List.length(b.xs)", "Set.size(b.tags) > 0",
            "Map.size(b.m) >= 1");

    @Test
    void everyRuleThatReadsASizeAgainstNoughtInFullStatesOneThing() {
        for (String condition : SIZES_AGAINST_NOUGHT) {
            Reading reading = reading(condition);
            List<Proposition> inFull = Pullback.byEachRule(reading.comparison(), reading.reads(),
                    reading.read()).stream()
                    .filter(stated -> !(stated instanceof Proposition.Unread))
                    .toList();
            assertTrue(inFull.size() >= 2, () -> condition + " is read in full by the emptiness"
                    + " check and by the cut both, so the two are held to one another: " + inFull);
            for (int size = 0; size <= 3; size++) {
                int at = size;
                boolean first = holdsAt(inFull.getFirst(), size);
                for (Proposition each : inFull) {
                    assertEquals(first, holdsAt(each, at), () -> condition + " at size " + at
                            + " is one thing by one rule and another by another: " + inFull);
                }
            }
        }
    }

    /**
     * A rule set aside leaves nothing behind: the second rule that takes this comparison meets a part
     * of its own on the way and is not kept, and what is stated turns on the first rule's part alone.
     */
    @Test
    void whatARuleSetAsideMetIsNoPartOfWhatIsStated() {
        String condition = "List.length(List.take(1, b.xs)) > 0";
        Reading reading = reading(condition);
        List<Proposition> byEach = Pullback.byEachRule(reading.comparison(), reading.reads(),
                reading.read());
        assertTrue(byEach.size() >= 2, () -> "more than one rule takes " + condition + ": "
                + byEach);
        Pullback.Pulled pulled = Pullback.ofATruth(reading.truth(), reading.reads(),
                reading.read(), Optional.empty());
        assertInstanceOf(Derivation.AnEmptinessCheck.class, pulled.meaning().how(),
                "where no rule reads it all, the first that takes it is kept");
        Proposition.Unread unread = assertInstanceOf(Proposition.Unread.class,
                pulled.proposition());
        assertEquals(new WhyUnread.NoLawFor(new ValueName.Stdlib.Operation("List", "take"),
                        AnswerAspect.EMPTINESS), unread.why());
        assertEquals(List.of(unread), pulled.leaves().stream().map(Pullback.Leaf::part).toList(),
                "the one part met is the kept rule's");
    }

    /** Whether {@code stated}, a relation over one size, holds where that size is {@code size}. */
    private static boolean holdsAt(Proposition stated, int size) {
        Proposition.Compared compared = assertInstanceOf(Proposition.Compared.class, stated,
                "a size compared with a number is a relation over the size");
        Relation.Affine affine = assertInstanceOf(Relation.Affine.class, compared.relation());
        LinearForm<?> form = affine.form();
        assertEquals(1, form.coefs().size(), () -> "a relation over the one size: " + form);
        ExactRatio value = form.coefs().values().iterator().next().times(ExactRatio.of(size))
                .flatMap(form.constant()::plus).orNull();
        assertNotNull(value, "a small size is held");
        return affine.proposition().holds(value.signum()) == compared.holds();
    }

    private record Reading(Core truth, StatedComparison comparison, InputReads reads,
                           InputReading read) {}

    /** {@code condition}, the condition of the one fork of {@code f}, as the reading meets it. */
    private static Reading reading(String condition) {
        String model = "module demo\n\n" + INPUT + """

                behavior f : (b: Box) -> Int
                let f (b) = if %s then 1 else 0
                """.formatted(condition);
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors(), () -> "the model compiles: " + condition);
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked("demo")).value();
        assertNotNull(checked, "the model under test compiles");
        AnalysisBody analysis = checked.analysisBodies().get("f");
        RuleReadingSource rules = RuleReadings.of(compilation, "demo");
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs("demo")).value().get("f");
        InputReads reads = InputReads.ofParametersWhereCallsStand(inputs.parameterReads(),
                inputs.declared(rules), ElementBindings.of(analysis, rules.newtypes()),
                inputs.dependencies());
        Core.If fork = assertInstanceOf(Core.If.class, Core.withoutStanding(analysis.core()),
                "the body is the fork");
        StatedComparison comparison = BooleanMeaning.asAComparison(fork.cond()).orElseThrow(
                () -> new AssertionError(condition + " is a comparison"));
        return new Reading(fork.cond(), comparison, reads, inputs.reading(rules));
    }
}
