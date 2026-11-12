package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.Measurement;
import souther.compiler.query.PartitionEvidence;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * A behavior over a string held by a format and a length rule is measured.
 *
 * <p>The behavior compares the string with the elements of a list, so what it asks of the
 * positions is which strings they hold. A position whose rules were each read by one of the two
 * readings and by neither together left that unanswered, and took the positions that relate to it
 * down with it.
 *
 * <p>{@code emails} holds any string and is what keeps the measure partial; what is asked is that
 * nothing else does.
 */
class AFormatAndALengthRuleTogetherLeaveThePartitionMeasuredTest {

    private static String modelWith(String email) {
        return """
                module bounded

                data Email = String invariant %s
                data Domains = List<String> invariant List.length(value) >= 1

                behavior f : (email: Email, domains: Domains, emails: List<String>) -> Bool
                let f (Email(email), Domains(domains), emails) =
                    List.any(own -> own == email, domains) || List.any(own -> own == email, emails)

                example f
                    | "domain" : (Email("a.com"), Domains([ "a.com" ]), []) -> true
                    | "email"  : (Email("x@b.com"), Domains([ "q" ]), [ "x@b.com" ]) -> true
                    | "none"   : (Email("x@b.com"), Domains([ "a.com" ]), [ "y@b.com" ]) -> false
                """.formatted(email);
    }

    private static final String A_FORMAT_AND_A_LENGTH =
            modelWith("String.matches(\"[^\\\\s]+\", value) && String.length(value) <= 254");

    @Test
    void theTwoRulesLeaveOnlyWhatTheUnconstrainedListLeavesUnanswered() {
        PartitionEvidence two = evidence(A_FORMAT_AND_A_LENGTH);

        assertInstanceOf(Measurement.Partial.class, two.partitioned(),
                "the measure was reached, with what the unconstrained list leaves of it");
        assertEquals(List.of("emails", "emails[*]"), notDerivable(two),
                "and the positions the two rules hold are answered");
        assertEquals(List.of("emails[*]"), unanswered(two));
    }

    private static List<String> notDerivable(PartitionEvidence found) {
        List<String> out = new ArrayList<>();
        found.notDerivable().forEach(each -> out.add(each.at().toString()));
        return out;
    }

    private static List<String> unanswered(PartitionEvidence found) {
        List<String> out = new ArrayList<>();
        found.unanswered().forEach(each -> out.add(each.at()));
        return out;
    }

    private static PartitionEvidence evidence(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        for (String module : compilation.modules()) {
            Map<String, PartitionEvidence> coverage =
                    compilation.db().ask(new Adequacy.Coverage(module)).value();
            if (coverage != null && coverage.get("f") != null) {
                return coverage.get("f");
            }
        }
        throw new AssertionError("the behavior was not measured");
    }
}
