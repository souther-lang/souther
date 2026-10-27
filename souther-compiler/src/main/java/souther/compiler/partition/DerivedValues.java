package souther.compiler.partition;

import souther.compiler.check.RuleCitation;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.types.ModelOccurrence;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Which computations of a value derived from several positions are cut at several places, decided
 * once for everything that reads them.
 *
 * <p>A computation cut at several places — a table of thresholds, a lookup in it read against every
 * row — does not divide the positions it is made of. A value of one position that settles the
 * comparison at one threshold leaves the next either way, so the classes that value parts a
 * position into state no outcome, and what is owed in their place is a weight for each position
 * ({@link Decided#replaced} says which). Cut at one place,
 * the values that settle the one comparison are the same outcome throughout, and the position keeps
 * its classes.
 *
 * <p><b>Only a comparison a body wrote draws a computation.</b> What says which computation it is,
 * is the copy of the comparison a call of its helper made ({@link LineOrigin#readAt}). A comparison
 * a clause of a declaration states has no call and names no copy, so it draws no computation: its
 * lines are never held apart, and its positions keep the classes they are divided into. That is the
 * contract of this decision for every reader that hands it lines, and not an omission of one.
 *
 * <p><b>One decision, and nothing derives it again.</b> The lines the classes were dropped for and
 * the computations owed weights are the one value this returns: a reader that worked the second out
 * from the borders afterwards would count thresholds over a different set of lines — a comparison
 * that draws no border, two readings folded into one — and could drop a position's classes with no
 * weight owed in their place.
 */
public final class DerivedValues {

    private DerivedValues() {
    }

    /**
     * The lines parting the values that settle a comparison of a derived value, held apart until
     * every comparison has been read: whether they part a class of their position is whether the
     * computation is cut at several places, which one comparison does not see.
     *
     * @param cuts     every computation the comparison cuts, and where
     * @param evidence what the lines add on the positions
     * @param between  the lines drawn between positions among them
     */
    public record Settling(List<DerivedValue.Cut> cuts, List<LineEvidence> evidence,
                           List<LineDrawn> between) {

        public Settling {
            cuts = List.copyOf(cuts);
            evidence = List.copyOf(evidence);
            between = List.copyOf(between);
        }
    }

    /**
     * What is left of the lines that were held apart, and the computations whose positions are
     * owed weights in place of the rest.
     *
     * @param evidence the lines on the positions of the computations cut at one place
     * @param between  the lines among them drawn between positions
     * @param replaced the computations cut at several places and the positions each is owed a
     *                 weight for
     */
    public record Decided(List<LineEvidence> evidence, List<LineDrawn> between,
                          List<DerivedValue.Replaced> replaced) {

        public Decided {
            evidence = List.copyOf(evidence);
            between = List.copyOf(between);
            replaced = List.copyOf(replaced);
        }
    }

    /**
     * Which computations are cut at several places by everything read, and what is left of the
     * lines held apart.
     *
     * @param settling every comparison's lines through a derived value, from every reader
     * @param between  every line drawn between positions, which cut computations as well
     */
    public static Decided decide(List<Settling> settling, List<LineDrawn> between) {
        Map<DerivedValue.Reading, Gathered> readings = new LinkedHashMap<>();
        for (Settling each : settling) {
            each.cuts().forEach(cut -> note(readings, cut));
        }
        for (LineDrawn each : between) {
            DerivedValue.cutsBy(each.by(), each.cuts().of(),
                    each.cuts().target().cut().canonical()).forEach(cut -> note(readings, cut));
        }
        // A comparison as a call reads it is cut at several places where more than one place on a
        // weighing of the positions is cut. The calls cut at the same places are one computation:
        // the rows on their borders are the same rows.
        Set<DerivedValue.Reading> several = new HashSet<>();
        Map<Group, List<DerivedValue.Reading>> computations = new LinkedHashMap<>();
        readings.forEach((reading, gathered) -> {
            if (gathered.places().size() > 1) {
                several.add(reading);
                computations.computeIfAbsent(new Group(reading.line(), gathered.places()),
                        _ -> new ArrayList<>()).add(reading);
            }
        });
        List<DerivedValue.Replaced> replaced = new ArrayList<>();
        computations.forEach((group, calls) -> {
            Set<NumericTerm> positions = new HashSet<>();
            Map<QuantityKey, LinearQuantity> forms = new LinkedHashMap<>();
            Set<RuleCitation> cited = new LinkedHashSet<>();
            for (DerivedValue.Reading call : calls) {
                Gathered gathered = readings.get(call);
                positions.addAll(gathered.positions());
                gathered.forms().forEach(forms::putIfAbsent);
                cited.addAll(gathered.cited());
            }
            replaced.add(new DerivedValue.Replaced(
                    new DerivedValue(group.line(),
                            calls.stream().map(DerivedValue.Reading::copy).toList()),
                    positions, List.copyOf(forms.values()), List.copyOf(cited)));
        });
        List<LineEvidence> evidence = new ArrayList<>();
        List<LineDrawn> kept = new ArrayList<>();
        for (Settling each : settling) {
            if (each.cuts().stream().noneMatch(cut -> several.contains(cut.reading()))) {
                evidence.addAll(each.evidence());
                kept.addAll(each.between());
            }
        }
        return new Decided(evidence, kept, replaced);
    }

    /**
     * {@code border} as the place of a computation it is, where it is one of a computation cut at
     * several places, and as it was otherwise.
     *
     * <p>Asked of the computations {@link #decide} returned and of no others, so that the borders
     * owed their points once for each place are the ones whose classes were not drawn.
     */
    static Border placed(Border border, List<DerivedValue.Replaced> replaced) {
        for (DerivedValue.Replaced each : replaced) {
            for (ModelOccurrence copy : each.value().copies()) {
                if (!each.value().isCutBy(border, copy)) {
                    continue;
                }
                List<DerivedValue.Cut> cuts = DerivedValue.cutsBy(border.origin(),
                        border.cut().of(), border.cut().cut().canonical());
                if (!cuts.isEmpty()) {
                    return border.atThreshold(
                            border.origin() instanceof LineOrigin.ComparisonOrigin comparison
                                    && comparison.read().writtenAgainst().isPresent()
                                    ? new ThresholdOfADerivedValue.WrittenAt(each.value(),
                                            comparison.read().writtenAgainst().get(),
                                            comparison.read().heldIn())
                                    : new ThresholdOfADerivedValue.CutAt(each.value(),
                                            cuts.getFirst().place()));
                }
            }
        }
        return border.origin() instanceof LineOrigin.ComparisonOrigin comparison
                && comparison.read().heldIn().isPresent()
                ? border.atThreshold(
                        new ThresholdOfADerivedValue.HeldIn(comparison.read().heldIn().get()))
                : border;
    }

    /** What the lines cutting one comparison as one call reads it come to. */
    private record Gathered(Set<DerivedValue.Place> places, Set<NumericTerm> positions,
                            Map<QuantityKey, LinearQuantity> forms, Set<RuleCitation> cited) {

        Gathered() {
            this(new HashSet<>(), new HashSet<>(), new LinkedHashMap<>(), new LinkedHashSet<>());
        }
    }

    /** Which calls are one computation: the same comparison, cut at the same places. */
    private record Group(AuthoredLine line, Set<DerivedValue.Place> places) {}

    private static void note(Map<DerivedValue.Reading, Gathered> readings, DerivedValue.Cut cut) {
        Gathered gathered = readings.computeIfAbsent(cut.reading(), _ -> new Gathered());
        gathered.places().add(cut.place());
        gathered.positions().addAll(cut.positions());
        gathered.forms().putIfAbsent(cut.place().expression(), cut.form());
        gathered.cited().add(cut.by().cited());
    }
}
