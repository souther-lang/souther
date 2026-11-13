package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.Measurement;
import souther.compiler.query.PartitionEvidence;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * A rule written on a record that reads one place alone is read as a rule of that place, as the
 * same rule written on the place's own type is.
 *
 * <p>What is held here is that the two forms are measured alike, so a later reading that measures
 * more of them holds as well. Which rule reads one place alone is held where it is answered
 * ({@code ARulePartReadsOnePlaceAloneOnlyWhereItReadsThatPlaceAndNothingElseTest}).
 */
class ALengthRuleOnARecordAboutOneFieldIsReadAsARuleOfThatFieldTest {

    private static final String THE_ISSUES_RECORD = """
            module bounded

            data Contact = { email: String, name: String }
                invariant String.length(email) <= 254

            behavior f : (contact: Contact, emails: List<String>) -> Bool
            let f (contact, emails) = List.any(own -> own == contact.email, emails)
            """;

    private static final String THE_ISSUES_NEWTYPE = """
            module bounded

            data Em = String invariant String.length(value) <= 254
            data Contact = { email: Em, name: String }

            behavior f : (contact: Contact, emails: List<String>) -> Bool
            let f (contact, emails) = List.any(own -> own == contact.email.value, emails)
            """;

    @Test
    void theRecordOfTheIssueReadsAsTheNewtypeDoes() {
        PartitionEvidence field = evidence(THE_ISSUES_NEWTYPE);
        PartitionEvidence record = evidence(THE_ISSUES_RECORD);

        assertInstanceOf(Measurement.Complete.class, field.partitioned(), "the control reads");
        assertEquals(measured(field), measured(record));
    }

    /**
     * What a behavior over a field {@code x} of a record is measured to be does not depend on
     * whether the rule on it is written on the record or on the field's own type.
     *
     * @param type   the type of {@code x} and of {@code y}
     * @param rule   the rule, {@code %1$s} standing for the value it is about
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
            new Shape("String", "String.length(%1$s) <= 20", "List<String>", List.of(
                    "String.length(r.x) > 10", "r.x == r.y", "String.startsWith(r.x, \"a\")",
                    "List.any(own -> own == r.x, other)",
                    "List.any(own -> own == String.lowercase(r.x), other)",
                    "r.x == r.y || List.any(own -> own == r.x, other)")),
            new Shape("String", "String.length(%1$s) <= 20\n    invariant String.length(%1$s) >= 1",
                    "List<String>", List.of(
                    "List.any(own -> own == r.x, other)", "r.x == r.y")),
            new Shape("String", "String.length(%1$s) >= 2", "String", List.of(
                    "r.x == other", "String.length(r.x) == String.length(other)",
                    "r.x == other || r.x == r.y")),
            new Shape("String", "String.length(%1$s) == 0", "List<String>", List.of(
                    "List.any(own -> own == String.lowercase(r.x), other)"
                            + " || List.any(own -> own == r.x, other)",
                    "List.any(own -> own == r.x, other)", "r.x == r.y")),
            new Shape("Int", "%1$s == 7", "Int", List.of(
                    "r.x == other", "r.x == other || r.y == other", "r.x + r.y == other")),
            new Shape("List<String>", "List.length(%1$s) <= 5", "String", List.of(
                    "List.length(r.x) > 2", "List.any(own -> own == other, r.x)",
                    "List.length(r.x) == List.length(r.y)", "r.x == r.y",
                    "List.any(own -> own == other, r.x) || List.any(own -> own == other, r.y)")),
            new Shape("List<Int>", "List.all(e -> e >= 0, %1$s)", "Int", List.of(
                    "List.any(e -> e > other, r.x)", "List.length(r.x) > 2",
                    "List.any(e -> e == other, r.x) || List.any(e -> e == other, r.y)")),
            new Shape("List<Int>", "List.all(e -> e >= 0 && e <= 99, %1$s)", "Int", List.of(
                    "List.any(e -> e > other, r.x)", "List.any(e -> e < other, r.x)")));

    @Test
    void aBehaviorIsMeasuredAsItIsWhereTheRuleIsWrittenOnTheRecordOrOnTheField() {
        List<String> differing = new ArrayList<>();
        for (Shape shape : SHAPES) {
            for (String body : shape.bodies()) {
                Said onRecord = measured(evidence(shape.onTheRecord(body)));
                Said onField = measured(evidence(shape.onTheField(body)));
                if (!onRecord.equals(onField)) {
                    differing.add(body + "\n  on the record " + onRecord + "\n  on the field  "
                            + onField);
                }
            }
        }
        assertEquals(List.of(), differing);
    }

    /** Each of two fields carries a rule of its own, and a behavior asks of each. */
    @Test
    void theRulesOfTwoFieldsAreEachReadAsTheRuleOfItsField() {
        String record = """
                module bounded

                data Contact = { email: String, name: String }
                    invariant String.length(email) <= 254 && String.length(name) <= 100

                behavior f : (contact: Contact, emails: List<String>) -> Bool
                let f (contact, emails) = %s
                """;
        String field = """
                module bounded

                data Em = String invariant String.length(value) <= 254
                data Nm = String invariant String.length(value) <= 100
                data Contact = { email: Em, name: Nm }

                behavior f : (contact: Contact, emails: List<String>) -> Bool
                let f (contact, emails) = %s
                """;
        List<String> differing = new ArrayList<>();
        for (String place : List.of("email", "name")) {
            Said onRecord = measured(evidence(record.formatted(
                    "List.any(own -> own == contact." + place + ", emails)")));
            Said onField = measured(evidence(field.formatted(
                    "List.any(own -> own == contact." + place + ".value, emails)")));
            if (!onRecord.equals(onField)) {
                differing.add(place + "\n  on the record " + onRecord + "\n  on the field  "
                        + onField);
            }
        }
        assertEquals(List.of(), differing);
    }

    /** The rule is on the record around the one that holds the field. */
    @Test
    void aRuleReadingAFieldOfAFieldIsReadAsTheRuleOfTheInnerRecord() {
        String outer = """
                module bounded

                data In = { a: Int, b: Int }
                data R = { inner: In, y: Int } invariant inner.a >= 0 && inner.a <= 99

                behavior f : (r: R, other: Int) -> Bool
                let f (r, other) = r.inner.a < other || r.y == other
                """;
        String inner = """
                module bounded

                data In = { a: Int, b: Int } invariant a >= 0 && a <= 99
                data R = { inner: In, y: Int }

                behavior f : (r: R, other: Int) -> Bool
                let f (r, other) = r.inner.a < other || r.y == other
                """;

        assertEquals(measured(evidence(inner)), measured(evidence(outer)));
    }

    /**
     * What a measurement says of the places of a behavior: whether it was reached, the classes of
     * each axis, and for every place what was left unanswered, not derivable, blocked or not
     * separated, and why. Not which rule it cites, which names the declaration it was written on.
     */
    private record Said(String state, Map<String, List<String>> classes, List<String> unanswered,
                        List<String> notDerivable, List<String> blocked,
                        List<String> notSeparated) {}

    private static Said measured(PartitionEvidence found) {
        Map<String, List<String>> classes = new TreeMap<>();
        found.axes().forEach(axis -> classes.put(axis.path(), axis.classes()));
        List<String> unanswered = new ArrayList<>();
        found.unanswered().forEach(each -> unanswered.add(each.at() + " "
                + each.asked().getClass().getSimpleName()));
        List<String> notDerivable = new ArrayList<>();
        found.notDerivable().forEach(each -> notDerivable.add(each.at() + " "
                + each.why().getClass().getSimpleName()));
        List<String> blocked = new ArrayList<>();
        found.blocked().forEach(each -> blocked.add(each.at() + " " + each.why()));
        List<String> notSeparated = new ArrayList<>();
        found.notSeparated().forEach(each -> notSeparated.add(each.at().toString()));
        return new Said(found.partitioned().getClass().getSimpleName(), classes, unanswered,
                notDerivable, blocked, notSeparated);
    }

    /** The places a measurement says something of are the same whether the rows a line asks for
     *  are searched or not, so they are not. */
    private static PartitionEvidence evidence(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
        ACompiledModel.compiles(compilation);
        assertFalse(compilation.modules().isEmpty(), "the model compiles");
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
