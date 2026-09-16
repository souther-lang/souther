package souther.compiler.meta;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.jvm.ClassFileImage;
import souther.compiler.query.Compilation;
import souther.compiler.query.Output;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a comparison leaves to a delegated equality is a form the census says a crossing can reach.
 *
 * <p>Two readings of one world, held together. One is worked out from the declarations — what a
 * crossing depends on, followed through everything it holds ({@link FormsACrossingCanReach}). The
 * other is what the comparison did: the models below are crossed and the walk says which forms it
 * handed over. A form the walk met and the census never named is the census answering about a
 * smaller world than the comparison lives in, which is the whole of what a census is for.
 *
 * <p>Told by the walk and not worked out again here. Whether a form reaches that branch is not a
 * property of its class — the comparison passes over some forms, has an arm for others, reads
 * through containers, and refuses two sides of different classes before it gets there — so a second
 * reading of which forms go that way would be a second author of the decision, and the two would
 * answer differently the first time either moved.
 *
 * <p>A build is crossed against itself. What is being read is which forms the walk goes to, and it
 * goes to the same ones whatever it decides about them; two builds that differ would stop at the
 * first thing they differ about and read less.
 */
class WhatTheComparisonLeftToADelegatedEqualityIsAFormItCanReachTest {

    /** A model reaching what a declaration holds: a rule over a written number, a field of a
     *  declared type, a helper, a newtype, and a case of the language's own. */
    private static final String MODEL = """
            module example.crossed
            import String ( length )

            data Title = String
                invariant length(value) > 0

            data Price = Decimal
                invariant value > 0.00m

            data Todo = { title: Title, price: Price, done: Bool, note: Option<Title> }

            behavior rename : (t: Todo, to: Title) -> Todo
                constructs Todo

            let rename (t, to) = Todo { title = to, price = t.price, done = t.done, note = t.note }
            """;

    /**
     * Every form the walk handed to a delegated equality is one the census reaches.
     *
     * <p>The other way round is left open. The census is over what a declaration can hold and a run
     * meets what these models happen to write, so a form nobody wrote here is reached by the census
     * and by no walk — which is the census doing its job rather than a disagreement.
     */
    @Test
    void everyFormLeftToADelegatedEqualityIsOneTheCensusReaches() {
        Set<Class<?>> handedOver = leftToADelegatedEquality();
        Set<Class<?>> canReach = FormsACrossingCanReach.taken().reached();

        List<String> metAndNeverNamed = new ArrayList<>(new TreeSet<>(handedOver.stream()
                .filter(form -> !canReach.contains(form))
                .map(Class::getName).toList()));

        assertEquals(List.of(), metAndNeverNamed,
                "the comparison handed these to a delegated equality and the census over what a"
                        + " crossing can reach does not name them, so whatever that census says is"
                        + " said about a smaller world than the one the comparison walks");
    }

    /**
     * The control: the reading is wired to the walk that decides.
     *
     * <p>Without it the check above is an emptiness passing for an agreement — a reading connected
     * to nothing reports no form met, and no form met is contained in anything. The witness is one
     * form this model is certain to cross by: what a field's type is declared by is a declaration
     * of a module, and the comparison holds two of those by a delegated equality.
     */
    @Test
    void andTheReadingIsConnectedToTheWalkThatDecides() {
        Set<Class<?>> handedOver = leftToADelegatedEquality();

        assertFalse(handedOver.isEmpty(),
                "a reading that saw the comparison hand nothing over is a reading of nothing, and"
                        + " what it would then say about the census is true of any census at all");
        assertTrue(handedOver.contains(TypeSymbol.AtModule.class),
                "a field's type is declared somewhere, and which declaration that is crosses as the"
                        + " identity it is, compared by the equality of that identity");
    }

    /** Which forms one crossing of this model handed to a delegated equality. */
    private static Set<Class<?>> leftToADelegatedEquality() {
        PublishedClasses declared = declarationsOf(MODEL);
        Set<Class<?>> handedOver = new LinkedHashSet<>();
        Agreement said = DeclarationAgreement.of("example.crossed", "rename", declared, declared,
                DefaultStdlib.get(), handedOver::add);

        assertEquals(Agreement.Agree.class, said.getClass(),
                "a build crossed against itself agrees, and a crossing that stopped early read"
                        + " less than the walk this is about");
        return handedOver;
    }

    /** The classes one build of {@code source} emits, read for what they were stamped with. */
    private static PublishedClasses declarationsOf(String source) {
        Compilation compiled = Compilation.ofSource(source, "Main");
        Map<String, ClassFileImage> classes = compiled.db().ask(new Output.All()).value();
        assertEquals(List.of(), refused(compiled), "the model this is measured against compiles");
        return ModulePath.of(classes).declarations();
    }

    /** What a compile refused, as codes — nothing, for the model measured here. */
    private static List<String> refused(Compilation compiled) {
        return compiled.diagnostics().values().stream().flatMap(List::stream)
                .filter(d -> d.diagnostic().severity() == souther.compiler.diag.Severity.ERROR)
                .map(d -> String.valueOf(d.diagnostic().code())).toList();
    }

}
