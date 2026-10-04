package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.DeclaredSig;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.revision.RevisionKnowledge;
import souther.compiler.types.Type;

import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * What stands for a record is composed once for a revision, however many readings of the same
 * source ask for it.
 *
 * <p>A search asks for a position's values from every point and every settling it visits, and each
 * asking reads in a reading of its own: a reading is a capability, made where it is wanted, so two
 * askings are two of them. What stands for a record is about the record and its rules, so it is
 * worked out for the first and lent to the rest.
 */
class ARecordIsComposedOnceHoweverOftenASearchAsksForItTest {

    /** A position one of whose cases is a record, which is composed to stand for that case. */
    private static final String A_RECORD_CASE = """
            module example.orders

            data Grade = Low | Middle | High

            data Card = { grade: Grade, qty: Int }

            data Cash

            data Payment = Card | Cash

            data Ok

            behavior take : (p: Payment) -> Ok

            let take (p) = Ok
            """;

    @Test
    void twoReadingsOfOneSourceComposeTheRecordOnce() {
        Compilation compilation = compiled();
        RuleReadingSource rules = rulesOf(compilation);
        Type payment = paymentOf(compilation);

        long before = RevisionKnowledge.timesDone(Partitions.ARecordComposed.class);
        List<FixtureTemplate> first = Partitions.representativesOf(payment,
                RuleReadingContext.of(rules, ReadAs.THE_COMPILATION_DOES,
                        compilation.db().readings()), null, Set.of());
        List<FixtureTemplate> second = Partitions.representativesOf(payment,
                RuleReadingContext.of(rules, ReadAs.THE_COMPILATION_DOES,
                        compilation.db().readings()), null, Set.of());

        assertFalse(first.isEmpty(), "a payment has values to stand for it");
        assertEquals(first, second, "and the same ones from either reading");
        assertEquals(1, RevisionKnowledge.timesDone(Partitions.ARecordComposed.class) - before,
                "the card was composed for the first reading and lent to the second");
    }

    /**
     * The control: a reading with no revision behind it composes the record each time.
     *
     * <p>Without it, the count above would say as much about a representative that never composed
     * the record as about one whose composing was kept.
     */
    @Test
    void readingsThatKeepNothingComposeItEachTime() {
        Compilation compilation = compiled();
        RuleReadingSource rules = rulesOf(compilation);
        Type payment = paymentOf(compilation);

        long before = RevisionKnowledge.timesDone(Partitions.ARecordComposed.class);
        Partitions.representativesOf(payment,
                RuleReadingContext.unshared(rules, ReadAs.THE_COMPILATION_DOES), null, Set.of());
        Partitions.representativesOf(payment,
                RuleReadingContext.unshared(rules, ReadAs.THE_COMPILATION_DOES), null, Set.of());

        assertEquals(2, RevisionKnowledge.timesDone(Partitions.ARecordComposed.class) - before);
    }

    private static Compilation compiled() {
        Compilation compilation = Compilation.ofSource(A_RECORD_CASE, "Main");
        compilation.answerEverything();
        return compilation;
    }

    private static RuleReadingSource rulesOf(Compilation compilation) {
        return RuleReadings.of(compilation, compilation.modules().get(0));
    }

    private static Type paymentOf(Compilation compilation) {
        Map<String, DeclaredSig> sigs = compilation.db()
                .ask(new Bodies.DeclaredSignatures(compilation.modules().get(0))).value();
        assertNotNull(sigs, "the model did not compile");
        return sigs.get("take").inputs().get(0).type();
    }
}
