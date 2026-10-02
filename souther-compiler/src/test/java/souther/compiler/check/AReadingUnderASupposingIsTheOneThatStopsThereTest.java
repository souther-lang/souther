package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.meta.ModulePath;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A reading a supposing hands a declaration says what a reading of that declaration stopping at the
 * supposed names says, whichever name beneath it the reading was made for.
 *
 * <p>A supposing reads a newtype that writes nothing as the one beneath it, down to the first name
 * supposed to have a value. Lent past that name, a declaration would be read with the rules under it
 * — the rules the supposing was about — and told it has no value by them. What the readings say is
 * compared rather than which name they were made for, because that is what a count reads off them;
 * the comparison is made against a reading made for the declaration itself, which shares nothing.
 *
 * <p>Asked of every declaration under every one name supposed, in both orders, since what a
 * supposing lends depends on which name of a chain it read first.
 */
class AReadingUnderASupposingIsTheOneThatStopsThereTest {

    /**
     * A chain of names that write nothing over one whose rules leave it no value, and a ring of
     * such names with one more worn over it. Supposing a name in the middle of the chain has a value
     * leaves every name above it with one; lent the reading of a name below, they would have none.
     */
    private static final String MODULE = """
            module demo

            data Empty = Int
                invariant none = value >= 2 && value <= 1

            data X0 = Empty
            data X1 = X0
            data X2 = X1
            data X3 = X2

            data R1 = R2
            data R2 = R3
            data R3 = R1
            data Into = R1
            """;

    private static final List<String> NAMES =
            List.of("Empty", "X0", "X1", "X2", "X3", "R1", "R2", "R3", "Into");

    @Test
    void everyDeclarationIsLentWhatItsOwnReadingUnderTheSupposingSays() {
        Compilation compilation = Compilation.ofSources(List.of(MODULE), ModulePath.EMPTY);
        compilation.answerEverything();
        RuleReadingContext reading = RuleReadingContext.of(RuleReadings.of(compilation, "demo"),
                ReadAs.THE_COMPILATION_DOES, compilation.db().readings());
        List<String> backwards = new ArrayList<>(NAMES);
        Collections.reverse(backwards);
        int lentPastTheSupposing = 0;
        for (String supposed : NAMES) {
            for (List<String> order : List.of(NAMES, backwards)) {
                Supposing supposing = Supposing.of(Set.of(declared(supposed)));
                for (String asked : order) {
                    if (asked.equals(supposed)) {
                        continue;
                    }
                    TypeSymbol.AtModule named = declared(asked);
                    Optional<Emptiness> lent = saidBy(
                            supposing.readingOf(named, reading), named, reading, supposing);
                    Optional<Emptiness> own = saidBy(InvariantChecker.readFields(
                            named, reading, Map.of(), supposing.reach()), named, reading,
                            supposing);
                    assertEquals(own, lent, () -> asked + " under " + supposed
                            + " supposed was lent a reading that says something else");
                    if (own.isEmpty() && asked.startsWith("X")) {
                        lentPastTheSupposing++;
                    }
                }
            }
        }
        assertTrue(lentPastTheSupposing > 0,
                "no name of the chain has a value under any supposing, so nothing here could tell"
                        + " a reading lent past the supposed name from one that stops there");
    }

    /** Whether the rules {@code read} holds leave {@code named} no value, and what shows it. */
    private static Optional<Emptiness> saidBy(DeclarationReading read, TypeSymbol.AtModule named,
                                              RuleReadingContext reading, Supposing supposing) {
        return FieldDomains.of(read, reading, supposing.reach())
                .holdsNothing(reading.readings().of(named.key()));
    }

    private static TypeSymbol.AtModule declared(String declaration) {
        return TypeSymbols.declared(new TypeKey("demo", declaration));
    }
}
