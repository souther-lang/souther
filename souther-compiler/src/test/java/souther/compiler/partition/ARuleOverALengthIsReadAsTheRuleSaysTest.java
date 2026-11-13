package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.TestDay;
import souther.compiler.carrier.Membership;
import souther.compiler.check.DeclaredSig;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.TypeCardinality;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.Position;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.values.Value;
import souther.compiler.values.ValuesAtLengths;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import java.util.function.Predicate;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A rule over the length of a string, alone or beside the strings it names or a pattern it
 * matches, leaves the strings the rule says and no other: the classes of strings a position can
 * be equal to hold the strings the rule allows, the strings written for them are such, the
 * lengths held are the ones the rule leaves, and a position the rule leaves a value is shown to
 * hold one.
 *
 * <p>The rules are drawn from a seed, each as the text the model is written in and the predicate
 * the rule means, so that the answer of every string in a pool is worked out from the rule and
 * not from its reading. A rule a reading does not read is no failure — the reading says less — but
 * one it reads is read as the predicate says.
 */
class ARuleOverALengthIsReadAsTheRuleSaysTest {

    private record Rule(String text, Predicate<String> allows) {

        Rule and(Rule other) {
            return new Rule("(" + text + " && " + other.text + ")",
                    each -> allows.test(each) && other.allows.test(each));
        }

        Rule or(Rule other) {
            return new Rule("(" + text + " || " + other.text + ")",
                    each -> allows.test(each) || other.allows.test(each));
        }
    }

    private static final String LENGTH = "String.length(value)";

    private static final List<String> OPERATORS = List.of("<=", ">=", "<", ">", "==", "/=");

    /** The strings each rule is asked of: every length up to twelve, and some with letters. */
    private static final List<String> POOL = new ArrayList<>();

    static {
        for (int length = 0; length <= 12; length++) {
            POOL.add("a".repeat(length));
        }
        POOL.addAll(List.of("ab", "b", "aab", "bab", "abc", "abcd", "xy", "x"));
    }

    private static int length(String text) {
        return text.codePointCount(0, text.length());
    }

    private static Rule bound(String operator, int than) {
        Predicate<String> allows = switch (operator) {
            case "<=" -> each -> length(each) <= than;
            case ">=" -> each -> length(each) >= than;
            case "<" -> each -> length(each) < than;
            case ">" -> each -> length(each) > than;
            case "==" -> each -> length(each) == than;
            default -> each -> length(each) != than;
        };
        return new Rule(LENGTH + " " + operator + " " + than, allows);
    }

    private static Rule bounds(Random random, int depth) {
        if (depth == 0 || random.nextInt(3) == 0) {
            return bound(OPERATORS.get(random.nextInt(OPERATORS.size())), random.nextInt(7));
        }
        Rule left = bounds(random, depth - 1);
        Rule right = bounds(random, depth - 1);
        return random.nextBoolean() ? left.and(right) : left.or(right);
    }

    private static Rule equalTo(String text) {
        return new Rule("value == \"" + text + "\"", each -> each.equals(text));
    }

    private static Rule notEqualTo(String text) {
        return new Rule("value /= \"" + text + "\"", each -> !each.equals(text));
    }

    private static Rule matching(String pattern) {
        return new Rule("String.matches(\"" + pattern + "\", value)",
                each -> each.matches(pattern));
    }

    private static List<Rule> rules() {
        Random random = new Random(7);
        List<Rule> rules = new ArrayList<>();
        // A choice between lengths beside strings the set holds whole, a set beside a hole past
        // everything it holds, and a choice one of whose alternatives leaves no length.
        rules.add(equalTo("abc").or(equalTo("abcd"))
                .and(bound("==", 4).or(bound("<=", 2))));
        rules.add(equalTo("abcd").and(bound("/=", 5)));
        rules.add(bound(">", 5).and(bound("<=", 0)).or(bound("<", 6)));
        for (int at = 0; at < 24; at++) {
            rules.add(bounds(random, 2));
        }
        List<Rule> sets = List.of(equalTo("abc"), equalTo("abc").or(equalTo("abcd")),
                notEqualTo("aa"), equalTo("abcd").or(equalTo("xy")).or(equalTo("a")),
                notEqualTo("abc"));
        for (int at = 0; at < 15; at++) {
            rules.add(sets.get(at % sets.size()).and(bounds(random, 1)));
        }
        List<String> patterns = List.of("a+", "[ab]+", "a*b?", "[ab]*");
        for (int at = 0; at < 12; at++) {
            rules.add(matching(patterns.get(at % patterns.size())).and(bounds(random, 1)));
        }
        return rules;
    }

    private static String model(String rule, String example) {
        return """
                module plain

                data Code = String
                    invariant %s

                behavior f : (code: Code, other: String) -> Bool
                let f (Code(code), other) = code == other

                example f
                    | "same"  : (Code("%s"), "%<s") -> true
                """.formatted(rule, example);
    }

    @Test
    void whatAReadRuleLeavesIsWhatItSays() {
        List<String> wrong = new ArrayList<>();
        int read = 0;
        int asked = 0;
        for (Rule rule : rules()) {
            String example = POOL.stream().filter(rule.allows()).findFirst().orElse(null);
            if (example == null) {
                continue;
            }
            boolean ofTheLengthsAlone = !rule.text().contains("value")
                    && !rule.text().contains("String.matches");
            if (ofTheLengthsAlone) {
                asked++;
            }
            Compilation model = ACompiledModel.answered(model(rule.text(), example));
            String module = model.modules().get(0);
            RuleReadingContext reading = RuleReadingContext.unshared(
                    RuleReadings.of(model, module), ReadAs.THE_COMPILATION_DOES, TestDay.TODAY);
            Partitions.Partitioning divided =
                    model.db().ask(new Adequacy.Divided(module, "f")).value();
            for (Axis axis : divided.axes()) {
                if (axis.path().toString().equals("other")) {
                    classesAreWhatTheRuleAllows(rule, axis, reading, wrong);
                }
            }
            Map<String, DeclaredSig> sigs =
                    model.db().ask(new Bodies.DeclaredSignatures(module)).value();
            InputDomain input = InputDomain.of(sigs.get("f"), reading,
                    TypeCardinality.Counts.workedOutIn(reading), Membership.none());
            if (!StringsReached.of(input.positions()).mandatoryPositionsHoldAValue()) {
                continue;
            }
            if (ofTheLengthsAlone) {
                read++;
            }
            Position code = input.positions().stream()
                    .filter(each -> each.path().toString().equals("code")).findFirst().get();
            lengthsHeldAreTheLengthsTheRuleLeaves(rule, code, wrong);
        }
        assertEquals(List.of(), wrong);
        assertTrue(read * 4 >= asked * 3,
                "most rules over the lengths alone are read: " + read + " of " + asked);
    }

    private static void classesAreWhatTheRuleAllows(Rule rule, Axis axis,
                                                    RuleReadingContext reading,
                                                    List<String> wrong) {
        for (PartitionClass each : axis.classes()) {
            boolean can = each.label().contains("can be");
            Partitions.standingFor(each.representatives(), reading, Set.of()).values()
                    .forEach(value -> {
                        String literal = value.text();
                        String written = literal.substring(1, literal.length() - 1)
                                .replace("\\t", "\t");
                        if (can != rule.allows().test(written)) {
                            wrong.add(each.label() + " is written at " + length(written)
                                    + " under " + rule.text());
                        }
                    });
            Recognition is = each.recognises() instanceof Recognition.Under(var _, var inner)
                    ? inner : each.recognises();
            if (!(is instanceof Recognition.OfASet(ValuesAtLengths values))) {
                continue;
            }
            for (String text : POOL) {
                if (values.has(new Value.Text(text)) && can != rule.allows().test(text)) {
                    wrong.add(each.label() + " holds " + length(text) + ":" + text + " under "
                            + rule.text());
                }
            }
        }
    }

    /**
     * Where the rule says nothing of the strings themselves, the lengths held are the lengths it
     * leaves, each asked of a string of that many letters.
     */
    private static void lengthsHeldAreTheLengthsTheRuleLeaves(Rule rule, Position code,
                                                              List<String> wrong) {
        if (rule.text().contains("value") || rule.text().contains("String.matches")) {
            return;
        }
        StringsHeld.Held held = StringsHeld.held(code);
        if (held == null) {
            return;
        }
        for (int length = 0; length <= 14; length++) {
            if (held.lengths().holds(BigInteger.valueOf(length))
                    != rule.allows().test("a".repeat(length))) {
                wrong.add("length " + length + " is held wrongly under " + rule.text());
            }
        }
    }
}
