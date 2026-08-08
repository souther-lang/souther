package souther.compiler.report;

import souther.compiler.observe.Incompleteness;

import java.util.Locale;

/**
 * What a reason reads as to a person.
 *
 * <p>An {@link Incompleteness} is data rather than a sentence, which is what lets a build count and
 * match on it. Two things print one for a reader — the report, and the note beside the rows
 * {@code --generate} writes — and both printed the enum's own name for a while. That told an author
 * with a type error in front of them that their runtime was missing, the code having been named
 * after one of the things it covers.
 *
 * <p>One wording, written once. Two renderers of the same fact drift, and the two here are read
 * side by side in the same terminal.
 *
 * <p><b>The rule this is held to.</b> A sentence here is keyed on the code and nothing else, so it
 * may say only what is true at <em>every</em> place that writes that code. The code is not what
 * happened; the producer is, and two producers writing one code mean two different things by it.
 * Where a consequence holds at one producer and not another, it belongs to the producer and cannot
 * be recovered from the code — the value would have to carry it. Nothing here may reach for it.
 *
 * <p>That rule is the whole of what this class gets wrong when it gets something wrong, and it has
 * already done so twice: once by writing a sentence for every code without reading any producer,
 * and once by giving a linkage failure the consequence its first producer has and its other two do
 * not.
 */
final class Reasons {

    /**
     * What happened, said as what happened — and no further than every producer agrees.
     *
     * <p>The three below have been read against theirs. {@code ROW_UNDECIDED} has one producer;
     * {@code OBSERVATION_ABSENT} has two and they mean the same thing; {@code LINKAGE_FAILED} has
     * three — an example that would not run, a fill that could not build its candidates, and a
     * boundary that could not build one — which agree that the classes would not link and disagree
     * about what did not happen next, so that is where the sentence stops.
     *
     * <p>The rest keep the shape they had, which asserts nothing the code does not already say.
     * Writing sentences for those wants the same walk done for each, and it turns up more than it
     * looks like it will: the subject of a search limit is a count and a phrase rather than a name,
     * and the code for a lost probe mapping is written wherever the instrumented classes could not
     * be made, which is a good deal wider than a mapping that was lost.
     */
    static String said(Incompleteness gap) {
        return switch (gap.code()) {
            case OBSERVATION_ABSENT -> String.format(
                    "no rows were read from `%s`, so what they cover is unknown", gap.subject());
            case LINKAGE_FAILED -> String.format("the classes for `%s` would not link",
                    gap.subject());
            case ROW_UNDECIDED -> String.format(
                    "a row of `%s` did not come back, so what it covers is unknown", gap.subject());
            case VALUE_UNREADABLE, VALUE_TRUNCATED, PROBE_MAPPING_LOST, SEARCH_LIMIT, AXIS_OMITTED ->
                    String.format("%s (%s)", gap.subject(),
                            gap.code().name().toLowerCase(Locale.ROOT));
        };
    }

    private Reasons() {}
}
