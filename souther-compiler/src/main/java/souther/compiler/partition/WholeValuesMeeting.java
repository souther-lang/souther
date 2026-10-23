package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.numeric.CanonicalOrder;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LaterNumbersEliminated;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rel;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

/**
 * A whole value for each number some statements are of, built so that every statement holds at
 * them, and then worked out at them to show it does.
 *
 * <p>Built in two steps. A statement that a sum of several numbers is one value says what one of
 * them is once the others are given: {@code z + w == 2} puts {@code z} at {@code 2 - w}, and the
 * other statements are read of that instead of {@code z}, so {@code z - w == 0} comes to
 * {@code 2 - 2w == 0}, a statement of {@code w} alone. Each such number is worked out last, from
 * the values of the others. The rest are given values one at a time, each from exactly the whole
 * numbers the statements of it and of the numbers already given leave it ({@link WholeNumbersLeft}),
 * within where the region puts it and the ends the declarations leave it.
 *
 * <p>Among those statements are the ones the bounds on the numbers not given yet leave it, those
 * numbers eliminated ({@link LaterNumbersEliminated}). A bound on a sum of numbers not given yet
 * reaches the first of them only so: under
 * {@code z + w >= 2 && z + w <= 2 && z - w >= 0 && z - w <= 0} neither the region nor any one
 * statement puts {@code z} at one, and the four with {@code w} eliminated do. So a value given
 * leaves every later number some rational value, though not always a whole one, and where none is
 * left nothing is shown, never that no value is. The value given is the one the statements alone
 * leave first ({@link WholeNumbersLeft#one}) wherever the eliminated bounds leave it too, and
 * only where they do not, the first they leave. Every value some choice of values from the
 * statements alone reaches is then reached with the bounds, because the bounds are implied by the
 * statements and so hold at any values that meet them: the elimination can add values found, and
 * take none away. Every statement is worked out at the values built,
 * and each value is held to the ends the declarations leave it, so what is built is a proof wherever
 * it comes back ({@link #holdsAt}) and the way it was built decides only whether one is found.
 */
final class WholeValuesMeeting {

    private WholeValuesMeeting() {
    }

    /** What looking for values comes to, and how many pairs of bounds the elimination took. */
    sealed interface Witness {

        /** How many pairs of bounds the elimination put together
         *  ({@link LaterNumbersEliminated#pairsCombined}). */
        long pairsCombined();

        /** A whole value for each number, at which every statement holds. */
        record Found(Map<NumericTerm, ExactRatio> values, long pairsCombined) implements Witness {

            public Found {
                values = Map.copyOf(values);
            }
        }

        /**
         * None shown, which is not that none is.
         *
         * @param pastThePairs whether the elimination stopped short at the pairs it was allowed
         *                     ({@link LaterNumbersEliminated.Why#PAIRS}), which may be why
         */
        record NotShown(boolean pastThePairs, long pairsCombined) implements Witness {
        }
    }

    private static final Witness NONE_SHOWN = new Witness.NotShown(false, 0);

    /**
     * A whole value for each number {@code statements} are of, at which every one of them holds,
     * where one is shown.
     *
     * @param region   where the way puts the numbers
     * @param declared the ends between which the declarations leave a number every value and no
     *                 other, or null where that is not shown, which shows nothing of it
     * @param pairs    how many pairs of bounds the elimination may put together
     */
    static Witness of(List<TakenConstraint.Affine> statements, SearchRegion region,
                      Function<NumericTerm, NumericDomain.Bounds> declared, long pairs) {
        // A number's value turns on which numbers came before it, so they come in one order the
        // numbers themselves decide.
        CanonicalOrder<NumericTerm> inOrder = NumericTerm.inOneOrder();
        List<TakenConstraint.Affine> left = new ArrayList<>(statements);
        List<Map.Entry<NumericTerm, LinearForm<NumericTerm>>> fixedBy = new ArrayList<>();
        for (TakenConstraint.Affine equality = aFixingOfSeveral(left); equality != null;
                equality = aFixingOfSeveral(left)) {
            left.remove(equality);
            NumericTerm term = firstOf(equality.form(), inOrder);
            LinearForm<NumericTerm> standsAt = solvedFor(equality.form(), term);
            NumericDomain.Bounds ends = declared.apply(term);
            if (standsAt == null || ends == null) {
                return NONE_SHOWN;
            }
            List<TakenConstraint.Affine> read = new ArrayList<>();
            for (TakenConstraint.Affine each : left) {
                LinearForm<NumericTerm> form = each.form().over(one -> one.equals(term) ? standsAt
                        : LinearForm.atom(one));
                if (form == null) {
                    return NONE_SHOWN;
                }
                read.add(new TakenConstraint.Affine(form, each.rel()));
            }
            List<TakenConstraint.Affine> within = between(standsAt, ends);
            if (within == null) {
                return NONE_SHOWN;
            }
            read.addAll(within);
            left = read;
            fixedBy.add(Map.entry(term, standsAt));
        }
        Set<NumericTerm> given = new LinkedHashSet<>();
        left.forEach(each -> given.addAll(each.form().coefs().keySet()));
        fixedBy.forEach(each -> given.addAll(each.getValue().coefs().keySet()));
        fixedBy.forEach(each -> given.remove(each.getKey()));
        List<NumericTerm> terms = inOrder.walking(given, term -> term);
        List<LaterNumbersEliminated.Bound<NumericTerm>> bounds = new ArrayList<>();
        left.forEach(each -> boundsOf(each, bounds));
        for (NumericTerm term : terms) {
            NumericDomain.Bounds ends = declared.apply(term);
            List<TakenConstraint.Affine> within = ends == null ? null
                    : between(LinearForm.atom(term), ends);
            if (within == null) {
                return NONE_SHOWN;
            }
            within.forEach(each -> boundsOf(each, bounds));
        }
        LaterNumbersEliminated<NumericTerm> eliminated =
                LaterNumbersEliminated.of(bounds, terms, pairs);
        Witness notShown = new Witness.NotShown(
                eliminated instanceof LaterNumbersEliminated.StoppedShort<NumericTerm> stopped
                        && stopped.why() == LaterNumbersEliminated.Why.PAIRS,
                eliminated.pairsCombined());
        List<List<LaterNumbersEliminated.Bound<NumericTerm>>> levels = new ArrayList<>();
        switch (eliminated) {
            case LaterNumbersEliminated.Eliminated<NumericTerm> all -> levels.addAll(all.levels());
            // The numbers before the one not eliminated are given values where their own
            // statements and the region put them, which is all that is known of them.
            case LaterNumbersEliminated.StoppedShort<NumericTerm> stopped -> {
                for (int place = 0; place < stopped.place(); place++) {
                    levels.add(List.of());
                }
                levels.addAll(stopped.reached());
            }
            case LaterNumbersEliminated.NoneLeft<NumericTerm> _ -> {
                return notShown;
            }
        }
        Map<NumericTerm, ExactRatio> out = oneAtATime(terms, left, levels, region, declared);
        if (out == null) {
            return notShown;
        }
        // Each fixed number is read of numbers given or fixed after it, so the last comes first.
        for (int each = fixedBy.size() - 1; each >= 0; each--) {
            ExactRatio at = valueOf(fixedBy.get(each).getValue(), out);
            if (at == null || !at.isWhole()) {
                return notShown;
            }
            out.put(fixedBy.get(each).getKey(), at);
        }
        // What was built is worked out against everything it is to meet, so that how it was built
        // decides only whether one is found.
        boolean met = statements.stream().allMatch(each -> holdsAt(each, out))
                && out.entrySet().stream().allMatch(each ->
                        declared.apply(each.getKey()) instanceof NumericDomain.Bounds ends
                                && ends.admits(each.getValue()));
        return met ? new Witness.Found(out, eliminated.pairsCombined()) : notShown;
    }

    /** Adds to {@code into} the bounds {@code statement} states: none for a value held out, which
     *  leaves a sum on either side of it. */
    private static void boundsOf(TakenConstraint.Affine statement,
                                 List<LaterNumbersEliminated.Bound<NumericTerm>> into) {
        LinearForm<NumericTerm> form = statement.form();
        switch (statement.rel()) {
            case LT -> into.add(new LaterNumbersEliminated.Bound<>(form, true));
            case LE -> into.add(new LaterNumbersEliminated.Bound<>(form, false));
            case GT -> into.add(new LaterNumbersEliminated.Bound<>(form.negate(), true));
            case GE -> into.add(new LaterNumbersEliminated.Bound<>(form.negate(), false));
            case EQ -> {
                into.add(new LaterNumbersEliminated.Bound<>(form, false));
                into.add(new LaterNumbersEliminated.Bound<>(form.negate(), false));
            }
            case NE -> {
            }
        }
    }

    /** An equality among {@code statements} of two numbers or more, or null where none is. */
    private static TakenConstraint.Affine aFixingOfSeveral(List<TakenConstraint.Affine> statements) {
        return statements.stream().filter(each -> each.rel() == Rel.EQ
                && each.form().coefs().size() > 1).findFirst().orElse(null);
    }

    private static NumericTerm firstOf(LinearForm<NumericTerm> form,
                                       CanonicalOrder<NumericTerm> inOrder) {
        return inOrder.walking(form.coefs().keySet(), term -> term).getFirst();
    }

    /** What {@code term} stands at where {@code form} is nought, as a form of the others — or null
     *  where the arithmetic cannot say. */
    private static LinearForm<NumericTerm> solvedFor(LinearForm<NumericTerm> form,
                                                     NumericTerm term) {
        ExactRatio weight = form.coefs().get(term);
        LinearForm<NumericTerm> rest = form.over(one -> one.equals(term)
                ? LinearForm.constant(ExactRatio.ZERO) : LinearForm.atom(one));
        return rest == null ? null : rest.negate().dividedBy(weight).orNull();
    }

    /** That {@code form} stands within {@code ends}, as statements of it — or null where an end is
     *  no number, or the arithmetic cannot say. */
    private static List<TakenConstraint.Affine> between(LinearForm<NumericTerm> form,
                                                         NumericDomain.Bounds ends) {
        List<TakenConstraint.Affine> out = new ArrayList<>();
        for (Endpoint end : new Endpoint[] {ends.min(), ends.max()}) {
            if (end == null) {
                continue;
            }
            if (!(end.at() instanceof Count count)) {
                return null;
            }
            LinearForm<NumericTerm> from = form.plus(LinearForm.constant(count.exactly().negated()))
                    .orNull();
            if (from == null) {
                return null;
            }
            boolean least = end == ends.min();
            out.add(new TakenConstraint.Affine(from, least
                    ? end.inclusive() ? Rel.GE : Rel.GT
                    : end.inclusive() ? Rel.LE : Rel.LT));
        }
        return out;
    }

    /**
     * A whole number for each of {@code terms}, each where {@code region} puts it once the ones
     * before it stand at theirs, between the ends the declarations leave it, and among the whole
     * numbers the statements of it and of the numbers already given leave it, those at its own
     * place in {@code levels} among them — or null where one is not shown to be a number the
     * declarations leave every value between its ends, or none is left it.
     */
    private static Map<NumericTerm, ExactRatio> oneAtATime(
            List<NumericTerm> terms, List<TakenConstraint.Affine> statements,
            List<List<LaterNumbersEliminated.Bound<NumericTerm>>> levels, SearchRegion region,
            Function<NumericTerm, NumericDomain.Bounds> declared) {
        Map<NumericTerm, ExactRatio> out = new LinkedHashMap<>();
        SearchRegion given = region;
        for (int place = 0; place < terms.size(); place++) {
            NumericTerm term = terms.get(place);
            NumericDomain.Bounds ends = declared.apply(term);
            if (ends == null || !(given.projectionOf(term)
                    instanceof NumericDomain.FormProjection.Within(NumericDomain.Bounds put))) {
                return null;
            }
            WholeNumbersLeft left = WholeNumbersLeft.of(put.meet(ends));
            for (TakenConstraint.Affine each : statements) {
                if (left == null) {
                    return null;
                }
                left = leftBy(each, term, out, left);
            }
            if (left == null) {
                return null;
            }
            // The value the statements alone give is kept wherever the levels leave it, so a
            // value found without the elimination is found with it.
            BigInteger whole = left.one();
            WholeNumbersLeft within = left;
            for (LaterNumbersEliminated.Bound<NumericTerm> each : levels.get(place)) {
                if (within == null) {
                    return null;
                }
                within = leftBy(new TakenConstraint.Affine(each.form(), each.strict() ? Rel.LT
                        : Rel.LE), term, out, within);
            }
            if (within == null) {
                return null;
            }
            if (whole == null || !within.leaves(whole)) {
                whole = within.one();
            }
            if (whole == null) {
                return null;
            }
            out.put(term, ExactRatio.of(whole));
            given = given.given(term, Count.of(new BigDecimal(whole)));
        }
        return out;
    }

    /**
     * What {@code statement} leaves of {@code left}, the whole numbers {@code term} may be, where
     * every other number it is of stands at {@code values}: {@code left} itself where it does not
     * weigh {@code term} or weighs one not given yet, and null where the arithmetic cannot say.
     */
    private static WholeNumbersLeft leftBy(TakenConstraint.Affine statement, NumericTerm term,
                                           Map<NumericTerm, ExactRatio> values,
                                           WholeNumbersLeft left) {
        ExactRatio weight = statement.form().coefs().get(term);
        if (weight == null || weight.isZero()) {
            return left;
        }
        ExactRatio constant = statement.form().constant();
        for (Map.Entry<NumericTerm, ExactRatio> each : inOneOrder(statement.form())) {
            if (each.getKey().equals(term)) {
                continue;
            }
            ExactRatio value = values.get(each.getKey());
            if (value == null) {
                return left;
            }
            if (!(each.getValue().times(value) instanceof ExactAnswer.Held<ExactRatio>(
                    ExactRatio weighed))
                    || !(constant.plus(weighed) instanceof ExactAnswer.Held<ExactRatio>(
                            ExactRatio sum))) {
                return null;
            }
            constant = sum;
        }
        return left.meeting(weight, constant, statement.rel());
    }

    /** What {@code form} comes to with each number it is of at {@code values} — null where one is
     *  not there, or the arithmetic cannot say. */
    private static ExactRatio valueOf(LinearForm<NumericTerm> form,
                                      Map<NumericTerm, ExactRatio> values) {
        ExactRatio at = form.constant();
        for (Map.Entry<NumericTerm, ExactRatio> term : inOneOrder(form)) {
            ExactRatio value = values.get(term.getKey());
            if (value == null || !(term.getValue().times(value)
                    instanceof ExactAnswer.Held<ExactRatio>(ExactRatio weighed))
                    || !(at.plus(weighed) instanceof ExactAnswer.Held<ExactRatio>(ExactRatio sum))) {
                return null;
            }
            at = sum;
        }
        return at;
    }

    /**
     * The weights of {@code form} in the one order its numbers decide. An exact sum can fail part
     * of the way, a term too far apart in scale from the sum so far having no representation beside
     * it, so whether it fails turns on which terms came first, and a map's own order would make that
     * a matter of the map.
     */
    private static List<Map.Entry<NumericTerm, ExactRatio>> inOneOrder(
            LinearForm<NumericTerm> form) {
        return NumericTerm.inOneOrder().walking(form.coefs().entrySet(), Map.Entry::getKey);
    }

    /** Whether {@code statement} holds with each number it is of at {@code values} — false where
     *  one is not there, or the arithmetic cannot say. */
    static boolean holdsAt(TakenConstraint.Affine statement, Map<NumericTerm, ExactRatio> values) {
        ExactRatio at = valueOf(statement.form(), values);
        return at != null && statement.rel().holds(at.signum());
    }
}
