package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.Measurement;
import souther.compiler.query.PartitionEvidence;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A rule written on a record that reads one of its fields alone is read as a rule of that field,
 * as the same rule written on the field's own type is. A rule reading two of its fields together
 * still relates them.
 */
class ALengthRuleOnARecordAboutOneFieldIsReadAsARuleOfThatFieldTest {

    private static String contact(String rules) {
        return """
                module bounded

                data Contact = { email: String, name: String }
                    %s

                behavior f : (contact: Contact, emails: List<String>) -> Bool
                let f (contact, emails) = List.any(own -> own == contact.email, emails)

                example f
                    | "in"  : (Contact { email = "a@b", name = "a@b" }, [ "a@b" ]) -> true
                    | "out" : (Contact { email = "a@b", name = "a@b" }, [ "c@d" ]) -> false
                """.formatted(rules);
    }

    private static final String ON_THE_FIELD_TYPE = """
            module bounded

            data Em = String invariant String.length(value) <= 254
            data Contact = { email: Em, name: String }

            behavior f : (contact: Contact, emails: List<String>) -> Bool
            let f (contact, emails) = List.any(own -> own == contact.email.value, emails)

            example f
                | "in"  : (Contact { email = Em("a@b"), name = "a@b" }, [ "a@b" ]) -> true
                | "out" : (Contact { email = Em("a@b"), name = "a@b" }, [ "c@d" ]) -> false
            """;

    @Test
    void theRecordFormReadsAsTheFieldTypeFormDoes() {
        PartitionEvidence field = evidence(ON_THE_FIELD_TYPE);
        PartitionEvidence record = evidence(contact("invariant String.length(email) <= 254"));

        assertInstanceOf(Measurement.Complete.class, field.partitioned(), "the control reads");
        assertInstanceOf(Measurement.Complete.class, record.partitioned());
        assertEquals(unanswered(field), unanswered(record));
        assertEquals(notDerivable(field), notDerivable(record));
    }

    @Test
    void ruleOfEachFieldAloneAreReadAsRulesOfThoseFields() {
        PartitionEvidence evidence = evidence(contact(
                "invariant String.length(email) <= 254 && String.length(name) <= 100"));

        assertInstanceOf(Measurement.Complete.class, evidence.partitioned());
        assertEquals(List.of(), unanswered(evidence));
    }

    @Test
    void twoRulesOnOneFieldAreReadAsRulesOfThatField() {
        PartitionEvidence evidence = evidence(contact(
                "invariant String.length(email) <= 254\n    invariant String.length(email) >= 1"));

        assertInstanceOf(Measurement.Complete.class, evidence.partitioned());
        assertEquals(List.of(), unanswered(evidence));
    }

    @Test
    void aRuleReadingTwoFieldsTogetherStillRelatesThem() {
        PartitionEvidence evidence = evidence(contact(
                "invariant String.length(email) <= 254 && email == name"));

        assertInstanceOf(Measurement.FailedToMeasure.class, evidence.partitioned());
        assertTrue(unanswered(evidence).contains("emails[*] NothingClassifiesIt"),
                unanswered(evidence).toString());
    }

    @Test
    void aChoiceBetweenTwoFieldsIsNotARuleOfOneOfThem() {
        PartitionEvidence evidence = evidence(contact(
                "invariant String.length(email) <= 254 || String.length(name) <= 254"));

        assertInstanceOf(Measurement.FailedToMeasure.class, evidence.partitioned());
        assertTrue(unanswered(evidence).contains("emails[*] NothingClassifiesIt"),
                unanswered(evidence).toString());
    }

    @Test
    void aPartnerHeldByARecordRulePartsTheOtherSideAsTheFieldTypeFormDoes() {
        String record = """
                module bounded
                data EmpId = String invariant String.length(value) >= 1
                data Pending = { me: EmpId, boss: EmpId } invariant String.length(boss.value) >= 2
                behavior f : (p: Pending, approver: EmpId) -> Bool
                let f (p, approver) = approver == p.boss
                example f
                    | "a" : (Pending { me = EmpId("a"), boss = EmpId("bb") }, EmpId("bb")) -> true
                    | "b" : (Pending { me = EmpId("a"), boss = EmpId("bb") }, EmpId("c")) -> false
                """;
        String newtype = """
                module bounded
                data EmpId = String invariant String.length(value) >= 1
                data Boss = String invariant String.length(value) >= 2
                data Pending = { me: EmpId, boss: Boss }
                behavior f : (p: Pending, approver: EmpId) -> Bool
                let f (p, approver) = approver.value == p.boss.value
                example f
                    | "a" : (Pending { me = EmpId("a"), boss = Boss("bb") }, EmpId("bb")) -> true
                    | "b" : (Pending { me = EmpId("a"), boss = Boss("bb") }, EmpId("c")) -> false
                """;
        PartitionEvidence onTheRecord = evidence(record);
        PartitionEvidence onTheField = evidence(newtype);

        assertEquals(classesOf(onTheField), classesOf(onTheRecord));
        assertEquals(List.of("approver: x can be p.boss", "approver: x is never p.boss"),
                classesOf(onTheRecord).get("approver"));
    }

    private static Map<String, List<String>> classesOf(PartitionEvidence found) {
        Map<String, List<String>> out = new TreeMap<>();
        found.axes().forEach(axis -> out.put(axis.path(), axis.classes()));
        return out;
    }

    private static List<String> notDerivable(PartitionEvidence found) {
        List<String> out = new ArrayList<>();
        found.notDerivable().forEach(each -> out.add(each.at().toString()));
        return out;
    }

    private static List<String> unanswered(PartitionEvidence found) {
        List<String> out = new ArrayList<>();
        found.unanswered().forEach(each -> out.add(each.at() + " " + each.asked().getClass()
                .getSimpleName()));
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
