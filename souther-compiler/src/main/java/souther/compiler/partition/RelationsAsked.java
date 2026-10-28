package souther.compiler.partition;

import souther.compiler.inputs.InputReading;
import souther.compiler.meaning.Proposition;

import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.function.Supplier;

/**
 * What each comparison's relation asks of a row, worked out once for each of one reading.
 *
 * <p>A statement is asked of a row as the comparisons it is made of, and the statements a search
 * asks about are one another with a case more, so the same comparison is asked again with every
 * one of them. What it asks is a function of the comparison and the reading alone.
 *
 * <p>What is kept is the work and not the read it made. A read is told which copies of the model's
 * code it was read off by the place it stands in ({@link DemandReading.Projection}), and the first
 * place to tell a read is the one that stays told, so one read standing in two places would be
 * told what the first of them says. Each ask is handed a read of its own, made of the same demand.
 * A read of a kind that is not made again from its parts is worked out each time it is asked.
 *
 * <p>Of one reading, which is held and asked for: what a comparison asks is read against the
 * declarations of the input, and an answer under one reading is no answer under another
 * ({@link InputReading#derived}).
 */
final class RelationsAsked {

    private final Map<Proposition.Compared, DemandReading.Read> asked = new ConcurrentHashMap<>();

    /** What the comparisons over {@code read} ask of a row, kept for that reading. */
    static RelationsAsked of(InputReading read) {
        return read.derived(RelationsAsked.class, _ -> new RelationsAsked());
    }

    /**
     * What {@code compared} asks of a row, as {@code work} says the first time it is asked.
     *
     * <p>A read of its own each time, so that no two places hold one read.
     */
    DemandReading.Read of(Proposition.Compared compared, Supplier<DemandReading.Read> work) {
        DemandReading.Read had = asked.get(compared);
        if (had == null) {
            DemandReading.Read made = work.get();
            if (!(made instanceof DemandReading.Read.Demands
                    || made instanceof DemandReading.Read.Unread
                    || made instanceof DemandReading.Read.Settled)) {
                return made;
            }
            asked.put(compared, made);
            return afresh(made);
        }
        return afresh(had);
    }

    private static DemandReading.Read afresh(DemandReading.Read made) {
        return switch (made) {
            case DemandReading.Read.Demands(var demand) -> new DemandReading.Read.Demands(demand);
            case DemandReading.Read.Unread(var whys, var beside) ->
                    new DemandReading.Read.Unread(whys, beside);
            case DemandReading.Read.Settled(boolean thisWay) ->
                    new DemandReading.Read.Settled(thisWay);
            default -> throw new IllegalStateException(
                    "a read of this kind is not kept, so it is not made again: " + made);
        };
    }
}
