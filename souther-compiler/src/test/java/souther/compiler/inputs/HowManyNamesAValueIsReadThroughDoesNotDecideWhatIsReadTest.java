package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * How many names a value is read through does not decide what is read.
 *
 * <p>A name standing for another is the one thing a model may have any number of. A wrapper taken
 * apart, a helper applied, a total given a name before it is compared: each leaves one more name
 * between a rule and the position it is about, and none of them is a statement about the model. So
 * the rule read at one name deep and the rule read at sixteen are the same rule, and what is asked
 * for at the line it draws is the same three rows.
 *
 * <p>What this holds is the shape of the reading and not one model's answer. A walk that measures
 * how far it has come answers the short ones and gives up on the long ones, and every number it
 * could stop at is a model somebody may write — so the regression for the model that was reported
 * would go green again under a larger number, and this would not. The stopping law is where the walk
 * has been ({@link BindingTrail}), which no length reaches.
 *
 * <p><b>One shape per way the walk crosses to another expression.</b> Which models are grown is not
 * a matter of taste: the walk gets longer by a name standing for another and by an operation
 * answering the elements it was given, and a number put back on either is a number the other says
 * nothing about. So there is a model per crossing and a crossing added here is a model added — the
 * reading beside this one, of where in an element a closure's answer stands, crosses by names of its
 * own and states this law for itself.
 */
class HowManyNamesAValueIsReadThroughDoesNotDecideWhatIsReadTest {

    private static final String LINE = "List.sum(明細[*].金額) = 100000";

    /**
     * The same rule with {@code names} wrappers around the list, each taken apart where the behavior
     * takes its parameter.
     *
     * <p>Every wrapper is one more name between the total and the position its values stand at, and
     * none of them is a statement about the rule: a model naming its list twice over says what a
     * model naming it once says.
     */
    private static String model(int names) {
        StringBuilder out = new StringBuilder("""
                module example.through

                data 金額 = Int

                data 明細 = { 金額: 金額 }

                data 高額
                data 少額

                data 束1 = List<明細>
                """);
        for (int n = 2; n <= names; n++) {
            out.append("data 束%d = 束%d%n".formatted(n, n - 1));
        }
        out.append("%nbehavior 判定する : (明細: 束%d) -> 高額 | 少額%n".formatted(names));
        StringBuilder taken = new StringBuilder("件");
        for (int n = 1; n <= names; n++) {
            taken.insert(0, "束%d(".formatted(n)).append(")");
        }
        out.append("""

                let 判定する (%s) =
                    if List.sum(List.map(一件 -> 一件.金額.value, 件)) >= 100000
                    then 高額 else 少額

                example 判定する
                    | "ちょうど10万円なら高額" : (%s) -> 高額
                    | "1000円なら少額"        : (%s) -> 少額
                """.formatted(taken, wrapped(names, 100000), wrapped(names, 1000)));
        return out.toString();
    }

    /** One list of one detail of {@code amount}, under every wrapper the model declares. */
    private static String wrapped(int names, int amount) {
        StringBuilder out = new StringBuilder("[ 明細 { 金額 = 金額(%d) } ]".formatted(amount));
        for (int n = 1; n <= names; n++) {
            out.insert(0, "束%d(".formatted(n)).append(")");
        }
        return out.toString();
    }

    /**
     * The same rule with the list walked by {@code operations} that answer what they were given.
     *
     * <p>The other way a walk to a position gets longer. A {@code reverse} answers the elements it
     * was handed, so an element of one is an element of what went in, and the way to the position
     * runs through as many of them as the model wrote — none of which is a statement about the rule
     * either.
     */
    private static String walked(int operations) {
        StringBuilder walk = new StringBuilder("明細");
        for (int n = 0; n < operations; n++) {
            walk.insert(0, "List.reverse(").append(")");
        }
        return """
                module example.through

                data 金額 = Int

                data 明細 = { 金額: 金額 }

                data 高額
                data 少額

                behavior 判定する : (明細: List<明細>) -> 高額 | 少額

                let 判定する (明細) =
                    if List.sum(List.map(一件 -> 一件.金額.value, %s)) >= 100000
                    then 高額 else 少額

                example 判定する
                    | "ちょうど10万円なら高額" : ([ 明細 { 金額 = 金額(100000) } ]) -> 高額
                    | "1000円なら少額"        : ([ 明細 { 金額 = 金額(1000) } ])   -> 少額
                """.formatted(walk);
    }

    /** The line the threshold draws in {@code source}, where {@code said} is how long its way to the
     *  position is. */
    private static BorderAssessment totalsLine(String source, String said) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(),
                () -> "the model under test compiles at " + said);
        PartitionEvidence measured = compilation.db()
                .ask(new Adequacy.Coverage("example.through")).value().get("判定する");
        assertEquals(List.of(), measured.notRead().stream()
                        .filter(each -> each.reason() == souther.compiler.partition
                                .UndividedPosition.Reason.RULE_ABOUT_A_DERIVED_VALUE)
                        .map(PartitionEvidence.NotRead::at).toList(),
                () -> "no position is told the rule is about a value made from it at " + said);
        BorderAssessment line = Adequacy.readingsOf(compilation.db(), "example.through")
                .get("判定する").stream()
                .filter(each -> LINE.equals(each.label())).findFirst().orElse(null);
        assertNotNull(line, () -> "the threshold is a line at " + said);
        return line;
    }

    /** What the line comes to, as the two shapes below compare it. */
    private static String asked(BorderAssessment line) {
        return line.label() + " on " + line.axis();
    }

    /**
     * One name between, or sixteen: the same line, drawn where the same rule draws it.
     *
     * <p>The line and what it is drawn on. Whether a row can be written at a point of it is asked of
     * a search and of how much of a value a report reads, and those answer for themselves; what is
     * held here is that the rule was read, which is what every one of them is downstream of.
     */
    @Test
    void theSameRuleIsAskedForHoweverManyNamesStandBetween() {
        Map<Integer, String> asked = new LinkedHashMap<>();
        for (int names : new int[] {1, 4, 8, 16}) {
            asked.put(names, asked(totalsLine(model(names), names + " names")));
        }

        assertEquals(1, java.util.Set.copyOf(asked.values()).size(),
                () -> "one answer however many names stand between: " + asked);
    }

    /**
     * And one operation between the parameter and the walk, or sixteen.
     *
     * <p>The other crossing, which the wrappers above do not lengthen: there the way to the position
     * runs through names, and here through operations that answer the elements they were given. A
     * number put back on this one is a number the model above says nothing about.
     */
    @Test
    void theSameRuleIsAskedForHoweverManyOperationsTheListIsWalkedBy() {
        Map<Integer, String> asked = new LinkedHashMap<>();
        for (int operations : new int[] {1, 4, 8, 16}) {
            asked.put(operations,
                    asked(totalsLine(walked(operations), operations + " operations")));
        }

        assertEquals(1, java.util.Set.copyOf(asked.values()).size(),
                () -> "one answer however many operations the list is walked by: " + asked);
    }
}
