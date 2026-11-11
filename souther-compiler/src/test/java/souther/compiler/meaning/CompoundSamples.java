package souther.compiler.meaning;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * A statement of every kind that holds statements, around the ones a test hands it, so that a
 * walk over statements can be asked what it does at each kind with the same two parts.
 *
 * <p>The kinds are written out here and checked against the kinds {@link Proposition} permits
 * ({@link #COMPOUNDS} and {@link #LEAVES} together are all of them), so a kind added to it is a
 * kind every walk's table has to place.
 */
public final class CompoundSamples {

    private CompoundSamples() {
    }

    /** The kinds that hold statements, each of which {@link Proposition#partsHeld} opens. */
    public static final List<Class<? extends Proposition>> COMPOUNDS = List.of(
            Proposition.All.class, Proposition.Any.class, Proposition.WhereItAnswers.class,
            Proposition.Some.class, Proposition.OnAnApplication.class,
            Proposition.SoManyHold.class, Proposition.OfTheWays.class,
            Proposition.SomeReachable.class);

    /** The kinds that hold no statement. */
    public static final List<Class<? extends Proposition>> LEAVES = List.of(
            Proposition.Always.class, Proposition.Compared.class, Proposition.Truth.class,
            Proposition.InCases.class, Proposition.Present.class, Proposition.InTheStrings.class,
            Proposition.SameValue.class, Proposition.SameAsWritten.class,
            Proposition.StringInside.class, Proposition.LastToHold.class, Proposition.Unread.class, Proposition.Carried.class);

    /** The kinds {@link Proposition} permits. */
    public static Set<Class<?>> permitted() {
        return new LinkedHashSet<>(List.of(Proposition.class.getPermittedSubclasses()));
    }

    /** The kinds placed here. */
    public static Set<Class<?>> placed() {
        Set<Class<?>> out = new LinkedHashSet<>(COMPOUNDS);
        out.addAll(LEAVES);
        return out;
    }

    /**
     * A statement of {@code kind} holding {@code one}, and {@code other} where it holds a second
     * part, with {@code container} as the container of the one that names a container.
     *
     * <p>A statement over the ways its elements are kept is written out from {@code one} and
     * holds what that comes to; one over the nodes reachable holds {@code one} at a node and
     * {@code other} where there is nothing below it.
     */
    public static Proposition holding(Class<?> kind, Proposition one, Proposition other,
                                      DecisionSubject container) {
        if (kind == Proposition.All.class) {
            return new Proposition.All(List.of(one, other));
        }
        if (kind == Proposition.Any.class) {
            return new Proposition.Any(List.of(one, other));
        }
        if (kind == Proposition.WhereItAnswers.class) {
            return new Proposition.WhereItAnswers(one, other);
        }
        if (kind == Proposition.Some.class) {
            return new Proposition.Some(container, one, true);
        }
        if (kind == Proposition.OnAnApplication.class) {
            return new Proposition.OnAnApplication(List.of(one, other));
        }
        if (kind == Proposition.SoManyHold.class) {
            // Its statements are kept once, in the order of their keys.
            List<Proposition> inOrder = one.spelling().compareTo(other.spelling()) < 0
                    ? List.of(one, other) : List.of(other, one);
            return new Proposition.SoManyHold(inOrder, List.of(1, 2), List.of(1));
        }
        if (kind == Proposition.OfTheWays.class) {
            return WaysSamples.over(one);
        }
        if (kind == Proposition.SomeReachable.class) {
            return new Proposition.SomeReachable(TermPath.of("t"), TermPath.of("t"),
                    List.of("children"), one, Optional.of(other), true);
        }
        throw new IllegalArgumentException(kind + " holds no statement");
    }

    /** The kinds {@link #holding} puts {@code other} into as a part of its own. */
    public static final List<Class<? extends Proposition>> TWO_PARTS = List.of(
            Proposition.All.class, Proposition.Any.class, Proposition.WhereItAnswers.class,
            Proposition.OnAnApplication.class, Proposition.SoManyHold.class,
            Proposition.SomeReachable.class);

    /** {@code number >= 0} over the input's number at {@code at}. */
    public static Proposition.Compared numberAtLeastZero(String at) {
        Quantity number = new DecisionAtom.OfTheInput(new NumericTerm.ValueOf(TermPath.of(at)));
        Relation.OneWay<Quantity> oneWay = Relation.OneWay.of(
                new LinearForm<>(ExactRatio.ZERO, Map.of(number, ExactRatio.ONE)), Rel.GE);
        return new Proposition.Compared(
                new Relation.Affine(oneWay.form(), oneWay.proposition()), oneWay.holds());
    }

    /** A truth of the input at {@code at}, which a row answers. */
    public static Proposition truth(String at) {
        return new Proposition.Truth(new DecisionSubject.AnInput(TermPath.of(at)), true);
    }

    /** The {@code ordinal}th statement nothing read, which no row is asked. */
    public static Proposition unread(int ordinal) {
        return new Proposition.Unread(Optional.empty(), ordinal, new WhyUnread.NoNumberOnARun(),
                false, true);
    }
}
