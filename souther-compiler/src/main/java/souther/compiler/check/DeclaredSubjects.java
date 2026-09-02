package souther.compiler.check;

import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Set;

/**
 * Which numbers of a value the rules written on its type are about.
 *
 * <p>{@link DeclaredBounds}' question one step back. That one answers where the rules leave the
 * value, which every rule that places no end is absent from; this one answers what the rules are
 * written about, which a rule naming a value is as much a part of as a rule ordering the values
 * around one. A reader choosing which number a position is measured on wants the second: whether
 * some clause happened to place an end is a fact about the clauses beside it and about this
 * compiler's arithmetic, and neither decides what a position is.
 *
 * <p>A set and not a choice. Two numbers of one value can both be written about, which is a model
 * with nothing here to pick between — said as a set, the reader that has to choose is the one that
 * knows what it does where there is no choice to make.
 */
public final class DeclaredSubjects {

    /**
     * The numbers the rules on {@code type} and on the types it wraps are written about.
     *
     * @param measure the operation a number of the value is taken by, or null where no number is
     *                taken of it
     */
    public static Set<FieldDomains.CoordinateKind> of(Type type, Symbols symbols,
                                                      ValueName measure) {
        Set<FieldDomains.CoordinateKind> out = new LinkedHashSet<>();
        for (DeclaredClauses.Conjunct each : DeclaredClauses.of(type, symbols)) {
            ClauseSubject about = ClauseSubject.of(each.expr(), measure);
            if (about != null) {
                out.add(about.number());
            }
        }
        return Collections.unmodifiableSet(out);
    }

    private DeclaredSubjects() {}
}
