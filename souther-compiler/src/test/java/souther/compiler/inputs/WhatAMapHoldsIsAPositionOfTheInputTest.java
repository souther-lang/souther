package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.check.DeclaredSig;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.core.Core;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.types.Type;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a map holds is a position of the input, and one the rules of the input can name.
 *
 * <p>Asked here, where the reading of an input is made, and not of whatever goes on to ask about a
 * number there. A body handed a map's values compares them as numbers of this input, and every
 * reader after this one names such a number through a value whose rules reach it — so a map the
 * walk did not go into leaves a term at its values that no reader further on can name, and what
 * fails then is that reader, far from the cause.
 */
class WhatAMapHoldsIsAPositionOfTheInputTest {

    /** A map of numbers beside a field, and nothing the record says about either. */
    private static final String A_MAP_BESIDE_A_FIELD = """
            module example.beside

            data Usage = { counts: Map<String, Int>, atLeast: Int }

            data Taken

            behavior take : (u: Usage) -> Taken
            """;

    private static final TermPath VALUES = TermPath.of("u").then("counts").element();

    /** The walk goes into the map, and what stands at the element is what the map holds. */
    @Test
    void theValuesAreAPositionTheWalkReached() {
        Position values = read().inputs().at(VALUES);
        assertNotNull(values, "the walk read a position at the map's values");
        assertEquals(Type.INT, values.type(), "and it is what the map holds, not its key");
    }

    private static final TermPath KEYS = TermPath.of("u").then("counts").key();

    /** The keys are a position of their own, holding what the map is keyed by. */
    @Test
    void theKeysAreAPositionBesideTheValues() {
        InputDomain inputs = read().inputs();
        Position keys = inputs.at(KEYS);
        assertNotNull(keys, "the walk read a position at the map's keys");
        assertEquals(Type.STRING, keys.type(), "and it is what the map is keyed by");
        assertEquals(Type.INT, inputs.at(VALUES).type(),
                "beside the values, which stay what the map holds");
    }

    /**
     * The declarations say the same of the two paths, where a walk that stopped above them leaves
     * nothing else to say it: the keys are what the map is keyed by and the values are what it
     * holds.
     */
    @Test
    void theDeclarationsPutTheKeyTypeAtTheKeys() {
        Read read = read();
        DeclaredInput declared = DeclaredInput.of(read.sig(), read.rules());
        assertEquals(Type.STRING, declared.typeAt(KEYS), "a key is what the map is keyed by");
        assertEquals(Type.INT, declared.typeAt(VALUES), "and a value is what it holds");
    }

    /**
     * A body reading a key over a map an operation kept the keys of, bound to a name between them.
     *
     * <p>Read the way the body's own demand is read, over the tree the operations were expanded in.
     * There a walk over a map is a walk over the list of its entries, and what a closure is handed
     * is a place of a pair — so the key is read at the keys only where the list says its pairs are
     * the map's entries.
     */
    private static final String A_KEY_OVER_A_KEPT_MAP = """
            module example.kept

            data Usage = { counts: Map<String, Int> }

            behavior popular : (u: Usage) -> Map<String, Int>

            let popular (u) = {
                let selected = Map.filterEntries((_, v) -> v > 0, u.counts)
                Map.filterEntries((k, _) -> String.length(k) <= 8, selected)
            }
            """;

    @Test
    void aBodyNamesTheKeysThroughAMapAnOperationKeptThemIn() {
        List<TermPath> named = namedByTheBodyOf(A_KEY_OVER_A_KEPT_MAP);
        assertTrue(named.contains(KEYS),
                () -> "the key the second walk reads is a key of the input's map: " + named);
    }

    /** Every location the body of {@code popular} names, read the way its demand is read. */
    private static List<TermPath> namedByTheBodyOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
        assertNotNull(checked, "the model under test compiles");
        Core body = checked.behaviorBodies().get("popular");
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs(module)).value()
                .get("popular");
        InputReads reads = InputReads.ofParameters(inputs.parameterReads(), inputs.declared(rules),
                checked.elementBindings().get("popular"));
        return InputDemand.of(body, reads, rules.symbols(), rules.newtypes()).paths();
    }

    /** And a number there is one this input's rules can name, so it is asked about like any. */
    @Test
    void aNumberThereIsAskedAboutLikeAnyOther() {
        Read read = read();
        assertNotNull(read.inputs().quantities(read.rules())
                        .ordersOf(new NumericTerm.ValueOf(VALUES)).answered(),
                "an Int a map holds is measured on the order every Int is");
    }

    private record Read(InputDomain inputs, RuleReadingSource rules, DeclaredSig sig) {}

    private static Read read() {
        Compilation compilation = Compilation.ofSource(A_MAP_BESIDE_A_FIELD, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Map<String, DeclaredSig> sigs =
                compilation.db().ask(new Bodies.DeclaredSignatures(module)).value();
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        return new Read(InputDomain.of(sigs.get("take"),
                RuleReadingContext.unshared(rules, ReadAs.THE_COMPILATION_DOES)), rules,
                sigs.get("take"));
    }
}
