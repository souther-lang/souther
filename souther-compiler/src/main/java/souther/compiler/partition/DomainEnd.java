package souther.compiler.partition;

import souther.compiler.types.TypeSymbol;

import java.util.List;

/**
 * Where the rules leave a quantity off on one side, and which declarations took it in there.
 *
 * <p>The place is what a run stopping there is owed for: it is what every rule about the position
 * leaves together, and no one of them is the reason. Which declarations moved it is a different
 * question and is answered here beside the place rather than inside it — a run stopping at the same
 * value is the same thing to write a row for however the position came to stop there, and two
 * readings that disagree about who narrowed it are still one point.
 *
 * <p>Both travel together because both are known where the position was read, and the day they are
 * carried apart is the day something has to put them back together by what they have in common —
 * which is the value, and reading the declarations back off a value is what this exists to avoid.
 *
 * @param bound     where the rules leave off
 * @param narrowers the declarations that took the end in, which is empty where nothing did and the
 *                  end is the type's own or the order's
 */
public record DomainEnd(Bound bound, List<TypeSymbol.AtModule> narrowers) {

    public DomainEnd {
        if (bound == null) {
            throw new IllegalArgumentException("an end the rules leave is somewhere");
        }
        narrowers = List.copyOf(narrowers);
    }

    /** An end nothing took in, which is what a position no declaration relates to anything has. */
    public static DomainEnd at(Bound bound) {
        return bound == null ? null : new DomainEnd(bound, List.of());
    }

    /** Where {@code end} is, or null where there is no end that way. */
    public static Bound boundOf(DomainEnd end) {
        return end == null ? null : end.bound();
    }
}
