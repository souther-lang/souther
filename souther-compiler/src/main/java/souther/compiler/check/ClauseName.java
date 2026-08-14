package souther.compiler.check;

import java.util.Objects;

/**
 * The name an author wrote on an invariant clause.
 *
 * <p>A clause MAY be written without one, and a clause that was is still a clause: what a name
 * decides is whether a diagnostic can send a reader to it, not whether it is there. Held as a type
 * of its own so that the set of them a judgment carries says what it is a set of — a
 * {@code Set<String>} that came out empty reads as "no clause", which is the one thing it never
 * means.
 */
record ClauseName(String value) {

    ClauseName {
        Objects.requireNonNull(value, "a clause name is the name that was written");
    }

    @Override
    public String toString() {
        return value;
    }
}
