package souther.compiler.numeric;

import souther.compiler.numeric.AffineConstraint.Read;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.EnumSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Rules as a test writes them, and the whole-numbered points over a small range that satisfy them.
 *
 * <p>For the tests that hold what the closure and the reduction say to the points themselves. A rule
 * is written the way it reads — {@code 2a - b <= -3} — so a chosen case says on its face what it is,
 * and it is checked at a point by its own arithmetic rather than by anything under test.
 *
 * <p>What the chosen systems were held to: each change below was made to the code they read, one at
 * a time, and the tests named are the ones that refused it. A change of the systems is checked
 * against this list again.
 *
 * <pre>
 *   DifferenceBounds  a cycle summing to nought read as empty     WhatTheDifference…, ARuleOver…, OneState… (the points)
 *   DifferenceBounds  ends meeting at one value read as crossed   the same three
 *   DifferenceBounds  an edge keeps the first bound found for it  WhatTheDifference… (the path through a third)
 *   DifferenceBounds  a carried bound above: the last one wins    WhatTheDifference… (the points)
 *   DifferenceBounds  a difference not read through nought        WhatTheDifference… (the points)
 *   ClosedState       one round only                              OneState…aRoundReadsWhatTheRoundBeforeItLeft
 *   ClosedState       a product forgets that the rounds ran out   RulesNaming…theClosureOfBothHalves…
 *   ClosureQuestion   a rule joining two parts loses the first    the build itself (prove-the-library)
 *   AffineReduction   a hole at the floor not sided               ARuleOver…, TheSameRules… (written cases)
 *   AffineReduction   a bound above: the last one wins            the order tests of ARuleOver…, OneState…, TheSameRules…
 *   AffineReduction   the middle one of three rules passed over   ARuleOver…theOrder… (every order; a reversal misses it)
 *   AffineReduction   a rest never reached not made strict        ARuleOver…aBoundReachedByNothingMakesWhatFollowsStrict
 *   AffineReduction   ends meeting at one value read as empty     ARuleOver…, OneState… (the points)
 *   AffineReduction   a hole at the only value left kept          ARuleOver…, TheSameRules… (written cases)
 * </pre>
 *
 * <p>Two changes none of these refuse, since what they make wrong is how tight a state is and these
 * claim soundness of it: a box carried along a difference letting the last bound win, and a form two
 * rules leave nothing not being asked for.
 */
final class RulesAsWritten {

    private RulesAsWritten() {
    }

    /** {@code Σ coefs·position + constant  rel  0}, as it was written. */
    record Written(Map<String, ExactRatio> coefs, ExactRatio constant, Rel rel) {

        @Override
        public String toString() {
            StringBuilder out = new StringBuilder();
            coefs.forEach((position, weight) -> out.append(out.isEmpty() ? "" : " + ")
                    .append(weight).append(position));
            return out + " " + rel + " " + constant.negated();
        }
    }

    private static final Map<String, Rel> RELATIONS = Map.of(
            "<=", Rel.LE, "<", Rel.LT, ">=", Rel.GE, ">", Rel.GT, "=", Rel.EQ, "/=", Rel.NE);

    private static final Pattern TERM = Pattern.compile("(-?)(\\d*)([a-z]+)");

    /**
     * One rule read off {@code text}: terms of a whole weight and a position, joined by {@code +} and
     * {@code -} and separated by spaces, then a relation and a whole number.
     */
    static Written rule(String text) {
        Map<String, ExactRatio> coefs = new LinkedHashMap<>();
        long sign = 1;
        String[] tokens = text.trim().split("\\s+");
        for (int at = 0; at < tokens.length; at++) {
            String token = tokens[at];
            Rel rel = RELATIONS.get(token);
            if (rel != null) {
                if (at + 2 != tokens.length) {
                    throw new IllegalArgumentException("one number after the relation in `" + text + "`");
                }
                return new Written(coefs, ExactRatio.of(-Long.parseLong(tokens[at + 1])), rel);
            }
            if (token.equals("+") || token.equals("-")) {
                sign = token.equals("+") ? 1 : -1;
                continue;
            }
            Matcher term = TERM.matcher(token);
            if (!term.matches()) {
                throw new IllegalArgumentException("`" + token + "` is not a term in `" + text + "`");
            }
            long weight = term.group(2).isEmpty() ? 1 : Long.parseLong(term.group(2));
            weight = term.group(1).isEmpty() ? sign * weight : -sign * weight;
            if (coefs.put(term.group(3), ExactRatio.of(weight)) != null) {
                throw new IllegalArgumentException("`" + term.group(3) + "` twice in `" + text + "`");
            }
            sign = 1;
        }
        throw new IllegalArgumentException("no relation in `" + text + "`");
    }

    static List<Written> rules(String... texts) {
        List<Written> out = new ArrayList<>();
        for (String text : texts) {
            out.add(rule(text));
        }
        return List.copyOf(out);
    }

    /** {@code rules} with each of {@code positions} held between {@code low} and {@code high}. */
    static List<Written> boxed(List<Written> rules, List<String> positions, int low, int high) {
        List<Written> out = new ArrayList<>();
        for (String position : positions) {
            out.add(new Written(Map.of(position, ExactRatio.ONE), ExactRatio.of(-low), Rel.GE));
            out.add(new Written(Map.of(position, ExactRatio.ONE), ExactRatio.of(-high), Rel.LE));
        }
        out.addAll(rules);
        return out;
    }

    /**
     * The constraints {@code written} states.
     *
     * <p>A rule every value satisfies states nothing, and leaving it out leaves the points it is
     * checked against where they were. A rule no value satisfies, or one the arithmetic cannot write,
     * is refused: left out, the points would hold nothing and what is handed on would hold
     * something, and a test that asks only of the points that are left would pass over the
     * disagreement without asking anything. A test that draws such rules says what it owes for them,
     * through {@link #someRuleHoldsNever} or by reading through {@link #statedOnly}.
     */
    static List<AffineConstraint<String>> read(List<Written> written,
                                               Function<String, Granularity> spacing) {
        List<AffineConstraint<String>> out = new ArrayList<>();
        for (Written each : written) {
            switch (AffineConstraint.of(each.coefs(), each.constant(), each.rel(), spacing)) {
                case Read.Stated<String> stated -> out.add(stated.constraint());
                case Read.HoldsAlways<String> _ -> { }
                case Read.HoldsNever<String> _ -> throw new IllegalArgumentException(
                        "`" + each + "` holds at no value, so no constraint can stand for it");
                case Read.NotWorkedOut<String> unheld -> throw new IllegalArgumentException(
                        "`" + each + "` states a constraint the arithmetic cannot write: "
                                + unheld.why());
            }
        }
        return out;
    }

    /**
     * The constraints {@code written} states, leaving out every rule that states none: one every
     * value satisfies, one no value satisfies, and one the arithmetic cannot write.
     *
     * <p>For drawn rules handed to two readers that are held to each other and to nothing else, such
     * as a closure in one run and the same rules parted: both are handed the same list, so a rule left
     * out is left out of both, and no point is asked about that could disagree with what they hold.
     * A test that asks the points as well reads through {@link #read}.
     */
    static List<AffineConstraint<String>> statedOnly(List<Written> written,
                                                     Function<String, Granularity> spacing) {
        List<AffineConstraint<String>> out = new ArrayList<>();
        for (Written each : written) {
            if (AffineConstraint.of(each.coefs(), each.constant(), each.rel(), spacing)
                    instanceof Read.Stated<String> stated) {
                out.add(stated.constraint());
            }
        }
        return out;
    }

    /**
     * Whether a rule of {@code written} is one no value satisfies, as reading it decides.
     *
     * <p>For rules drawn rather than chosen, which come to such a rule now and then: there is
     * nothing to hand on for them, and what is owed instead is that the points hold nothing either.
     */
    static boolean someRuleHoldsNever(List<Written> written, Function<String, Granularity> spacing) {
        return written.stream().anyMatch(each -> AffineConstraint.of(each.coefs(), each.constant(),
                each.rel(), spacing) instanceof Read.HoldsNever<String>);
    }

    /**
     * {@code items} in every order there is.
     *
     * <p>A reversal leaves a middle rule in the middle, so a reader that answers differently only
     * where a later rule stands between two earlier ones is seen in some other order and not in
     * that one. The systems here hold four rules or fewer, which is twenty-four orders at most.
     */
    static <T> List<List<T>> everyOrder(List<T> items) {
        if (items.size() <= 1) {
            return List.of(List.copyOf(items));
        }
        List<List<T>> out = new ArrayList<>();
        for (int first = 0; first < items.size(); first++) {
            List<T> rest = new ArrayList<>(items);
            T taken = rest.remove(first);
            for (List<T> after : everyOrder(rest)) {
                List<T> order = new ArrayList<>();
                order.add(taken);
                order.addAll(after);
                out.add(order);
            }
        }
        return out;
    }

    /**
     * Every way of dealing {@code one} and {@code other} into one list with each kept in its own
     * order.
     */
    static <T> List<List<T>> everyInterleaving(List<T> one, List<T> other) {
        if (one.isEmpty() || other.isEmpty()) {
            List<T> out = new ArrayList<>(one);
            out.addAll(other);
            return List.of(out);
        }
        List<List<T>> out = new ArrayList<>();
        for (List<T> rest : everyInterleaving(one.subList(1, one.size()), other)) {
            List<T> dealt = new ArrayList<>();
            dealt.add(one.getFirst());
            dealt.addAll(rest);
            out.add(dealt);
        }
        for (List<T> rest : everyInterleaving(one, other.subList(1, other.size()))) {
            List<T> dealt = new ArrayList<>();
            dealt.add(other.getFirst());
            dealt.addAll(rest);
            out.add(dealt);
        }
        return out;
    }

    /**
     * Ways of dealing {@code one} and {@code other} into one list with each kept in its own order:
     * either list said whole at every place among the other's, and the two taken in turn.
     *
     * <p>A reader that answers differently where rules of one list stand between two of the other
     * is seen at every place that can happen, and one that answers differently where the two
     * alternate is seen in the turns. The count grows with the two lengths added rather than with
     * the number of every interleaving, which for two lists of seven is thousands. Where every
     * interleaving is no more than these, every interleaving is what comes back.
     */
    static <T> List<List<T>> eachWholeAtEveryPlace(List<T> one, List<T> other) {
        Set<List<T>> out = new LinkedHashSet<>();
        wholeAtEveryPlace(one, other, out);
        wholeAtEveryPlace(other, one, out);
        out.add(inTurn(one, other));
        out.add(inTurn(other, one));
        long every = 1;
        for (int taken = 1; taken <= other.size(); taken++) {
            every = every * (one.size() + taken) / taken;
        }
        return every <= out.size() ? everyInterleaving(one, other) : List.copyOf(out);
    }

    private static <T> void wholeAtEveryPlace(List<T> placed, List<T> among, Set<List<T>> out) {
        for (int at = 0; at <= among.size(); at++) {
            List<T> dealt = new ArrayList<>(among.subList(0, at));
            dealt.addAll(placed);
            dealt.addAll(among.subList(at, among.size()));
            out.add(dealt);
        }
    }

    /** Both lists in one, taken from each in turn. */
    static <T> List<T> inTurn(List<T> one, List<T> other) {
        List<T> out = new ArrayList<>();
        for (int at = 0; at < Math.max(one.size(), other.size()); at++) {
            if (at < one.size()) {
                out.add(one.get(at));
            }
            if (at < other.size()) {
                out.add(other.get(at));
            }
        }
        return out;
    }

    /** {@code items} said twice over. */
    static <T> List<T> twice(List<T> items) {
        List<T> out = new ArrayList<>(items);
        out.addAll(items);
        return out;
    }

    /**
     * Every relation the rules of {@code systems} are written with.
     *
     * <p>For a test to hold equal to all of {@link Rel}, so that a relation added to the language is
     * one a chosen system has to be written with before the test passes again. A list of chosen
     * cases is a copy of the relations nothing else compares against it.
     */
    static Set<Rel> relationsIn(List<List<Written>> systems) {
        Set<Rel> out = EnumSet.noneOf(Rel.class);
        systems.forEach(rules -> rules.forEach(each -> out.add(each.rel())));
        return out;
    }

    static Set<String> positionsOf(List<Written> rules) {
        Set<String> out = new LinkedHashSet<>();
        rules.forEach(each -> out.addAll(each.coefs().keySet()));
        return out;
    }

    /** Every whole-numbered point of {@code positions} in {@code [low, high]} that satisfies every
     *  rule as it was written. */
    static List<Map<String, Integer>> pointsSatisfying(List<Written> written, List<String> positions,
                                                       int low, int high) {
        List<Map<String, Integer>> out = new ArrayList<>();
        int[] at = new int[positions.size()];
        Arrays.fill(at, low);
        while (true) {
            Map<String, Integer> point = new LinkedHashMap<>();
            for (int i = 0; i < at.length; i++) {
                point.put(positions.get(i), at[i]);
            }
            if (written.stream().allMatch(rule -> holdsAt(rule, point))) {
                out.add(point);
            }
            int i = 0;
            while (i < at.length && at[i] == high) {
                at[i++] = low;
            }
            if (i == at.length) {
                return out;
            }
            at[i]++;
        }
    }

    static boolean holdsAt(Written rule, Map<String, Integer> point) {
        ExactRatio total = rule.constant();
        for (Map.Entry<String, ExactRatio> each : rule.coefs().entrySet()) {
            total = each.getValue().times(ExactRatio.of(point.get(each.getKey())))
                    .flatMap(total::plus).orNull();
        }
        return rule.rel().holds(total.signum());
    }

    /** Whether {@code value} lies on the admitted side of {@code cut}, above it where {@code above}
     *  and below it otherwise; no cut admits everything. */
    static boolean admits(ExactCut cut, ExactRatio value, boolean above) {
        if (cut == null) {
            return true;
        }
        int order = value.compareTo(cut.at());
        return above ? (order < 0 || (order == 0 && cut.inclusive()))
                : (order > 0 || (order == 0 && cut.inclusive()));
    }

    /**
     * Systems over {@code a}, {@code b} and {@code c}, each written for one way the reduction or the
     * closure can be wrong, and each said beside what it tells apart.
     *
     * <p>The reduction and the closure are held to the points over these, and the readers above them
     * to the same answers in every order the rules have ({@link #everyOrder}). A system that asks
     * about order holds two rules bounding one thing, so a reader that lets the last one win, or the
     * one said between, answers in some order differently.
     */
    static final List<List<Written>> OVER_THREE = List.of(
            // A sum read the other way, where the rest is b and not a again.
            rules("a + 2b <= 3"),
            // A difference held both ways: a cycle summing to nought, which leaves a value.
            rules("a - b = 0", "b + c <= 1"),
            // A position held at one value, whose two ends meet and do not cross.
            rules("a = 2", "a + b + c <= 0"),
            // A sum that leaves both its positions at the last value the range has.
            rules("a + b >= 8"),
            // A hole the sum runs both sides of, which bounds nothing.
            rules("a + b /= 0"),
            // A hole at the top of a sum and one at the floor of a position, which side them.
            rules("a + b /= 8", "a /= -4"),
            // Two rules bounding a above, the tighter said first.
            rules("a + b <= -2", "a + c <= 4", "b >= 0", "c >= -3"),
            // A rule over three positions whose rest two other sums bound below, apart: b + c at
            // two, and with c at most nought, b + 2c at three puts it at three.
            rules("a + b + c <= 3", "b + c >= 2", "b + 2c >= 3", "c <= 0"),
            // A weighted difference, which is a sum and no difference.
            rules("2a - b <= -3"),
            // Uneven weights and strict comparisons.
            rules("3a - 2c <= 1", "2b + 3c > 4", "-2a + b - c < 5"),
            // A sum nothing in the range reaches.
            rules("a + b <= -9"),
            // Two bounds on one sum, the tighter said first.
            rules("a + b <= 1", "a + b <= 3"),
            // A part a round finds holding nothing beside a position no rule relates to it.
            rules("a + c >= 9", "a <= 4", "c <= 4", "b >= 0"),
            // A part whose ends cross before any round, beside a part holding something.
            rules("a >= 3", "a <= 2", "b + c <= 1"));
}
