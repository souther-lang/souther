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

    /**
     * What a behavior over a record's field {@code x} is measured to be does not depend on whether
     * the rule on it is written on the record or on the field's own type.
     *
     * @param type   the type of {@code x} and of {@code y}
     * @param rule   the rule, {@code %s} standing for the value it is about
     * @param param  the parameter {@code other} is, as written after its name
     * @param bodies behaviors over {@code r.x}, {@code r.y} and {@code other}
     */
    private record Shape(String type, String rule, String param, List<String> bodies) {

        String onTheRecord(String body) {
            return """
                    module bounded
                    data R = { x: %s, y: %s } invariant %s
                    behavior f : (r: R, other: %s) -> Bool
                    let f (r, other) = %s
                    """.formatted(type, type, rule.formatted("x"), param, body);
        }

        String onTheField(String body) {
            return """
                    module bounded
                    data X = %s invariant %s
                    data R = { x: X, y: %s }
                    behavior f : (r: R, other: %s) -> Bool
                    let f (r, other) = %s
                    """.formatted(type, rule.formatted("value"), type, param,
                    body.replace("r.x", "r.x.value"));
        }
    }

    private static final List<Shape> SHAPES = List.of(
            new Shape("Int", "%1$s >= 0 && %1$s <= 120", "Int", List.of(
                    "r.x < 18", "r.x == other", "r.x + r.y < 100", "r.x < 18 || other > 5",
                    "r.x <= r.y", "r.x * 2 >= other", "Int.floorMod(r.x, 3) == other",
                    "r.x == 5 && r.y == other")),
            new Shape("String", "String.length(%s) <= 20", "List<String>", List.of(
                    "String.length(r.x) > 10", "r.x == r.y", "String.startsWith(r.x, \"a\")",
                    "List.any(own -> own == r.x, other)",
                    "List.any(own -> own == String.lowercase(r.x), other)",
                    "r.x == r.y || List.any(own -> own == r.x, other)")));

    @Test
    void aBehaviorIsMeasuredAsItIsWhereTheRuleIsWrittenOnTheRecordOrOnTheField() {
        List<String> differing = new ArrayList<>();
        for (Shape shape : SHAPES) {
            for (String body : shape.bodies()) {
                PartitionEvidence record = evidence(shape.onTheRecord(body));
                PartitionEvidence field = evidence(shape.onTheField(body));
                String onRecord = measured(record);
                String onField = measured(field);
                if (!onRecord.equals(onField)) {
                    differing.add(body + "\n  on the record " + onRecord + "\n  on the field  "
                            + onField);
                }
            }
        }
        assertEquals(List.of(), differing);
    }

    private static String measured(PartitionEvidence found) {
        return found.partitioned().getClass().getSimpleName() + " " + unanswered(found) + " "
                + classesOf(found);
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
