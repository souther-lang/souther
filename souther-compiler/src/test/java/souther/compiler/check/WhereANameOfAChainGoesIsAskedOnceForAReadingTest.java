package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.meta.ModulePath;
import souther.compiler.query.Compilation;
import souther.compiler.query.Front;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;

import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Whether a name of a chain goes somewhere is asked once per name for a reading, however many of
 * the reading's terms are read through it.
 *
 * <p>A value read under a chain of names is read through a projection as long as the chain, and a
 * reading of a chain whose every name writes a rule keys a term at every one of those rules — each
 * through a projection one name longer than the last. Asked again at every name of every projection,
 * one reading asks the square of the chain and a compile the cube. The projections share their
 * names, so a name is worked out once and every longer projection reads the answer.
 *
 * <p>Counted, not timed: what is held is how the asking grows with the chain.
 */
class WhereANameOfAChainGoesIsAskedOnceForAReadingTest {

    @Test
    void aChainTwiceAsLongIsAskedAboutNoMoreThanTwiceAsOften() {
        int shorter = askedReading(20);
        int longer = askedReading(40);

        assertTrue(shorter > 0, "a reading of the chain asks where its names go at all");
        assertTrue(longer <= 2 * shorter + 8,
                () -> "a chain of forty names was asked about " + longer + " times against "
                        + shorter + " for twenty, so each name is asked again for every term"
                        + " read through it");
    }

    /** How often one reading of the top of a chain of {@code length} names, each writing a rule,
     *  asks whether a declaration wears one value. */
    private static int askedReading(int length) {
        StringBuilder source = new StringBuilder("""
                module chain

                data T1 = Int
                    invariant value >= 1 && value <= 9
                """);
        for (int i = 2; i <= length; i++) {
            source.append("data T").append(i).append(" = T").append(i - 1).append('\n')
                    .append("    invariant value >= ").append(i % 3).append('\n');
        }
        Compilation compilation =
                Compilation.ofSources(List.of(source.toString()), ModulePath.EMPTY);
        compilation.answerEverything();
        assertEquals(List.of(), compilation.diagnostics().values().stream()
                        .flatMap(List::stream).map(each -> each.diagnostic().code()).toList(),
                "the model under test is a program that can be written");
        RuleReadingSource rules = RuleReadings.of(compilation, "chain");
        ReadingPolicy policy = compilation.db().ask(new Front.Reading()).value();
        AtomicInteger asked = new AtomicInteger();
        RuleReadingSource counting = new RuleReadingSource(rules.symbols(), rules.invariants(),
                rules.declarations(), declaration -> {
                    asked.incrementAndGet();
                    return rules.newtypes().of(declaration);
                }, rules.bindings(), rules.written());

        FieldDomains.of(TypeSymbols.declared(new TypeKey("chain", "T" + length)),
                RuleReadingContext.unshared(counting, policy));
        return asked.get();
    }
}
