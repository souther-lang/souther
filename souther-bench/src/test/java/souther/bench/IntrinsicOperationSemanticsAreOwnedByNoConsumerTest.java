package souther.bench;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.util.LinkedHashSet;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What is true of the language's operations is declared where nothing reads it, and the readers
 * depend on that rather than the other way round.
 *
 * <p>The arrangement this holds is one rule: an intrinsic fact about an operation never belongs to a
 * consumer. Promoting a fact when a second reader turns up leaves the structure that produced the
 * problem — a fact still arrives in whichever check needs it first and is moved out later by
 * whoever needs it second, so the same repair is owed again every time. {@code NumericMeasures} was
 * the first such promotion, and its own comment records what it was for: two lists of the same
 * operations disagreed, and a rule discharged in one place was reported in the other as a rule the
 * model does not state.
 *
 * <p>Read off the bytecode rather than the sources, because what reaches a type is four things and
 * not one ({@link Compiled}) and a javadoc naming a package is not a dependency on it.
 */
class IntrinsicOperationSemanticsAreOwnedByNoConsumerTest {

    private static final String SEMANTICS = "souther.compiler.semantics.";

    /** The packages that read the declarations. None of them may be read from there. */
    private static final Set<String> CONSUMERS =
            Set.of("souther.compiler.check.", "souther.compiler.partition.");

    /**
     * Nothing in the declarations reaches a reader of them.
     *
     * <p>A fact that reached back into a check would be a fact written for that check, which is what
     * giving them a home of their own was for. The direction is the whole of the arrangement: a
     * reader may know what an operation is, and what an operation is may not know who is asking.
     */
    @Test
    void whatIsTrueOfAnOperationDoesNotReachTheProceduresThatReadIt() throws IOException {
        Set<String> reaching = new LinkedHashSet<>();
        for (Compiled.Site site : Compiled.sites()) {
            if (!site.from().startsWith(SEMANTICS)) {
                continue;
            }
            if (CONSUMERS.stream().anyMatch(site.owner()::startsWith)) {
                reaching.add(site.at() + " -> " + site.owner());
            }
        }
        assertEquals(Set.of(), reaching,
                "a declaration reached a procedure that reads it. What holding a fact to the"
                        + " library takes belongs on the reader's side, and a fact that reaches for"
                        + " it is a fact written for whoever asked first");
    }

    /** And the declarations are reached, so the check above saw something rather than nothing. */
    @Test
    void theProceduresThatReadThemDoReachTheDeclarations() throws IOException {
        Set<String> reading = new LinkedHashSet<>();
        for (Compiled.Site site : Compiled.sites()) {
            if (site.owner().startsWith(SEMANTICS)
                    && CONSUMERS.stream().anyMatch(site.from()::startsWith)) {
                reading.add(site.from());
            }
        }
        assertTrue(reading.size() > 1,
                "the declarations are read by more than one procedure, which is what having a home"
                        + " of their own is for: " + reading);
    }
}
