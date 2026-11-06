package souther.compiler.meaning;

import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Rel;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.OptionalLong;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * How many ways the truths of some of the parts a case is taken apart on can come out together,
 * where the parts compare one number and so cannot come out every way.
 *
 * <p><b>What the numbers leave, and nothing of what a reading builds.</b> Two laws, each with the
 * parts it is about and the count it gives:
 *
 * <ul>
 *   <li><b>Ordered boundaries.</b> Comparisons of one affine form against constants, each an
 *       ordering ({@code >=}, {@code >}, {@code <=}, {@code <}): each comes out by which side of
 *       one point the form's value is on — at the point or not — so as many points as they make
 *       leave at most one way more than the points. A point is a constant and whether the value
 *       at it is on the side above, so {@code x > 0} and {@code x >= 0} turn at two points and
 *       come out three ways. Counted over the rationals: a form that takes whole values only, or
 *       fewer values than that, may come out fewer ways, and this is no more than the most.
 *       Equalities are not among them, nor forms that differ by more than their constant.</li>
 *   <li><b>Correlated remainders.</b> Comparisons of remainders of one dividend by one divisor:
 *       one remainder decides them all, so they come out as many ways as there are remainders
 *       that tell them apart, counted remainder by remainder as a count of consistent ways reads
 *       them ({@link NumericallyConsistentWays#remaindersWhereItHolds}).</li>
 * </ul>
 *
 * <p>Neither is a number of cases, nor of the ways a reading of the cases would be left with were
 * the model written otherwise: how a reading takes a statement apart does not follow from what
 * its numbers can be, and a statement with fewer comparisons may be taken apart into more ways.
 * So nothing here predicts a count after a rewrite.
 */
public final class WhatTheNumbersOfACaseLeave {

    private WhatTheNumbersOfACaseLeave() {
    }

    /** What the numbers leave of the parts {@code cases} is taken apart on, each law once for
     *  each number its parts compare, where at least two parts compare it. */
    static List<CaseExpansion.Diagnosis> of(DecidingCase.Cases cases) {
        Map<Spelling, Proposition> parts = partsOf(cases);
        List<CaseExpansion.Diagnosis> out = new ArrayList<>();
        out.addAll(orderedBoundaries(parts.values()));
        out.addAll(correlatedRemainders(parts.values()));
        return List.copyOf(out);
    }

    /** Every part a case of {@code cases} is taken apart on, held, each case read once. */
    private static Map<Spelling, Proposition> partsOf(DecidingCase.Cases cases) {
        Map<Spelling, Proposition> out = new LinkedHashMap<>();
        cases.fold(new DecidingCase.Cases.Fold<Boolean>() {
            @Override
            public Boolean one(DecidingCase.Cases.One one) {
                WhereEachLineDecides.partsHeldBy(one.condition()).forEach(out::putIfAbsent);
                return true;
            }

            @Override
            public Boolean eachOf(DecidingCase.Cases.EachOf node, List<Boolean> alternatives) {
                return true;
            }

            @Override
            public Boolean together(DecidingCase.Cases.Together node, List<Boolean> factors) {
                return true;
            }

            @Override
            public Boolean notTakenApart(DecidingCase.Cases.NotTakenApart notTakenApart) {
                return true;
            }
        });
        return out;
    }

    /** One point an ordering's truth turns at: the value, and whether the value itself is on
     *  the side above. */
    private record Point(ExactRatio at, boolean includesIt) {}

    private static List<CaseExpansion.Diagnosis> orderedBoundaries(
            Iterable<Proposition> parts) {
        Map<Map<Quantity, ExactRatio>, Set<Point>> points = new LinkedHashMap<>();
        Map<Map<Quantity, ExactRatio>, Integer> comparisons = new LinkedHashMap<>();
        for (Proposition part : parts) {
            if (!(part instanceof Proposition.Compared(Relation.Affine affine, boolean holds,
                    Spelling _)) || affine.form().coefs().isEmpty()) {
                continue;
            }
            Rel rel = holds ? affine.proposition() : affine.proposition().denied();
            ExactRatio at = affine.form().constant().negated();
            Point point = switch (rel) {
                case GE, LT -> new Point(at, true);
                case GT, LE -> new Point(at, false);
                case EQ, NE -> null;
            };
            if (point == null) {
                continue;
            }
            points.computeIfAbsent(affine.form().coefs(), _ -> new HashSet<>()).add(point);
            comparisons.merge(affine.form().coefs(), 1, Integer::sum);
        }
        List<CaseExpansion.Diagnosis> out = new ArrayList<>();
        points.forEach((form, at) -> {
            int compared = comparisons.get(form);
            if (compared > 1) {
                out.add(new CaseExpansion.OrderedBoundaries(spelled(form), compared, at.size(),
                        at.size() + 1));
            }
        });
        return out;
    }

    private static List<CaseExpansion.Diagnosis> correlatedRemainders(
            Iterable<Proposition> parts) {
        Map<List<Object>, List<Long>> holding = new LinkedHashMap<>();
        Map<List<Object>, Quantity.RemainderOfADividend> of = new LinkedHashMap<>();
        for (Proposition part : parts) {
            if (!(part instanceof Proposition.Compared(Relation.Affine affine, boolean _,
                    Spelling _)) || affine.form().coefs().size() != 1
                    || !(affine.form().coefs().keySet().iterator().next()
                            instanceof Quantity.RemainderOfADividend remainder)) {
                continue;
            }
            OptionalLong where = NumericallyConsistentWays.remaindersWhereItHolds(part);
            if (where.isEmpty()) {
                continue;
            }
            List<Object> dividend = List.of(remainder.dividend().coefs(), remainder.divisor());
            holding.computeIfAbsent(dividend, _ -> new ArrayList<>()).add(where.getAsLong());
            of.putIfAbsent(dividend, remainder);
        }
        List<CaseExpansion.Diagnosis> out = new ArrayList<>();
        holding.forEach((dividend, masks) -> {
            if (masks.size() < 2) {
                return;
            }
            int divisor = of.get(dividend).divisor().intValueExact();
            Set<List<Boolean>> ways = new HashSet<>();
            for (int remainder = 0; remainder < divisor; remainder++) {
                List<Boolean> truths = new ArrayList<>();
                for (long mask : masks) {
                    truths.add((mask >>> remainder & 1L) != 0);
                }
                ways.add(truths);
            }
            out.add(new CaseExpansion.CorrelatedRemainders(
                    spelled(of.get(dividend).dividend().coefs()), divisor, masks.size(),
                    ways.size()));
        });
        return out;
    }

    /** A form without its constant, as its quantities are spelled. */
    private static String spelled(Map<Quantity, ExactRatio> coefs) {
        return coefs.entrySet().stream()
                .sorted(Map.Entry.comparingByKey((one, other) ->
                        one.spelling().compareTo(other.spelling())))
                .map(each -> (each.getValue().equals(ExactRatio.ONE) ? ""
                        : each.getValue() + "·") + each.getKey().spelling())
                .collect(Collectors.joining(" + "));
    }
}
