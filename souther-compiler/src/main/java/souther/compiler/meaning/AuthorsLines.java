package souther.compiler.meaning;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Objects;

/**
 * What a reading of a comparison says of the lines its author drew: which of them each relation
 * it states is a place of and how it stands to each, and where a row takes the arms each of those
 * lines is under.
 *
 * <p>The two together because they are one walk of one derivation, and both are about one line as
 * this reading put it on the input. Which line it is stays the author's ({@link WrittenLine}): the
 * arms of the definition. Where those arms are taken is this reading's, since a call puts them on
 * the input: {@code minimum(term)} with an arm for each term takes the one returning 12 where
 * {@code term} is that term, and a line under that arm decides nowhere else, whichever other arms
 * return 12 as well.
 *
 * @param byRelation for each relation the comparison states, spelled as
 *                   {@link Proposition.Compared#heldSpelling}, the lines it is a place of and how it
 *                   stands to each
 * @param taken      for each line, where a row takes every arm it is under; a line under no arm
 *                   is taken wherever the comparison is
 */
public record AuthorsLines(Map<String, Map<WrittenLine, AuthoredPointMapping>> byRelation,
                           Map<WrittenLine, Proposition> taken) {

    public AuthorsLines {
        Objects.requireNonNull(byRelation, "a reading says which lines each relation is a place of");
        byRelation = Collections.unmodifiableMap(new LinkedHashMap<>(byRelation));
        taken = Collections.unmodifiableMap(new LinkedHashMap<>(taken));
    }

    /** The lines {@code relation} is a place of and how it stands to each, or null where the
     *  reading saw no step make it. */
    public Map<WrittenLine, AuthoredPointMapping> of(String relation) {
        return byRelation.get(relation);
    }

    /** Where a row takes every arm {@code line} is under. */
    public Proposition takenWhere(WrittenLine line) {
        return taken.getOrDefault(line, new Proposition.Always(true));
    }
}
