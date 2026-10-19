package souther.compiler.partition;

import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Rel;
import souther.compiler.types.ModelOccurrence;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * What statements joining relations come to on the classes of one axis: for each class, whether a
 * statement holds throughout it, fails throughout it, or is not settled there.
 *
 * <p>A relation is settled on the classes by the line some comparison drew for it
 * ({@link InteractionCells#sideOf}). One no line was drawn for — it decides nowhere, or it comes
 * out the same for every row — is not taken to be anything: it is settled only where a relation
 * that was drawn implies it or is implied by it, which is a fact about the two relations and
 * not about the reading. Where neither is so, it is unknown, and a statement that depends on it is
 * not settled.
 *
 * <p>Three values and not two. {@code a || b} with {@code b} unknown holds where {@code a} holds
 * and is unknown elsewhere; {@code a && b} fails where {@code a} fails and is unknown elsewhere.
 */
final class StatementsOnClasses {

    /**
     * What is known of a statement on each class.
     *
     * @param yes the classes it holds throughout
     * @param no  the classes it fails throughout; a class in neither is not settled
     */
    record Settled(boolean[] yes, boolean[] no) {}

    /**
     * Where a statement holds among the classes, and which comparisons of the model it accounts
     * for.
     *
     * @param holds     for each class, whether the statement holds throughout it
     * @param explained the comparisons every line of which, on this axis, a relation of the
     *                  statement is
     */
    record Evaluated(boolean[] holds, Set<ModelOccurrence> explained) {}

    /**
     * A relation of one quantity to a place, written {@code quantity over at}.
     *
     * @param minusConstant {@code at} times {@code perQuantity}, so that two of them are compared
     *                      without dividing
     * @param perQuantity   the positive weight of the quantity in the form
     */
    private record Ray(Quantity over, boolean up, boolean strict, ExactRatio minusConstant,
                       ExactRatio perQuantity) {

        /** Whether {@code this} holding implies {@code other} holding. */
        boolean implies(Ray other) {
            if (!over.equals(other.over) || up != other.up) {
                return false;
            }
            ExactRatio mine = minusConstant.times(other.perQuantity).orNull();
            ExactRatio theirs = other.minusConstant.times(perQuantity).orNull();
            if (mine == null || theirs == null) {
                return false;
            }
            int order = mine.compareTo(theirs);
            if (order == 0) {
                return !other.strict || strict;
            }
            return up ? order > 0 : order < 0;
        }
    }

    private final List<Axis> axes;
    private final int axis;
    private final int classes;
    /** Each relation, by its spelling held, with what is known of it on the classes. */
    private final Map<String, Settled> known = new LinkedHashMap<>();
    /** The relations a line was drawn for. */
    private final Set<String> drawn = new LinkedHashSet<>();
    /** The comparison whose one line stands for the one relation its applications state. */
    private ModelOccurrence soleLineOf;

    /**
     * @param statements the statements to be settled together, whose relations may imply one
     *                   another
     * @param states     the comparison of the model they are the applications of, or null where
     *                   they are not
     */
    StatementsOnClasses(List<Axis> axes, int axis, Collection<Proposition> statements,
                        ModelOccurrence states) {
        this.axes = axes;
        this.axis = axis;
        this.classes = axes.get(axis).classes().size();
        Map<String, Proposition.Compared> relations = new LinkedHashMap<>();
        statements.forEach(each -> collect(each, relations));
        // A comparison all of whose applications state one relation draws one line with no part
        // to name it: the line is that relation's. With two relations it names neither.
        boolean theOneLine = states != null && relations.size() == 1;
        Map<String, Ray> rays = new LinkedHashMap<>();
        relations.forEach((key, leaf) -> {
            Ray ray = rayOf(leaf);
            if (ray != null) {
                rays.put(key, ray);
            }
            Settled drawnAt = drawnFor(key, theOneLine ? states : null);
            if (drawnAt != null) {
                known.put(key, drawnAt);
                drawn.add(key);
            }
        });
        rays.forEach((key, ray) -> {
            if (!drawn.contains(key)) {
                known.put(key, impliedFor(key, ray, rays));
            }
        });
    }

    private static void collect(Proposition stated, Map<String, Proposition.Compared> out) {
        switch (stated) {
            case Proposition.Compared leaf -> out.putIfAbsent(leaf.heldKey(), leaf);
            case Proposition.All all -> all.parts().forEach(part -> collect(part, out));
            case Proposition.Any any -> any.parts().forEach(part -> collect(part, out));
            default -> { }
        }
    }

    /** The relation as a place on a quantity, or null where it is not one. */
    private static Ray rayOf(Proposition.Compared leaf) {
        if (!(leaf.relation() instanceof Relation.Affine affine)
                || affine.form().coefs().size() != 1) {
            return null;
        }
        Map.Entry<Quantity, ExactRatio> only = affine.form().coefs().entrySet().iterator().next();
        if (only.getValue().signum() <= 0) {
            return null;
        }
        Rel rel = affine.proposition();
        if (rel == Rel.EQ || rel == Rel.NE) {
            return null;
        }
        boolean up = rel == Rel.GE || rel == Rel.GT;
        return new Ray(only.getKey(), up, rel == Rel.GT || rel == Rel.LT,
                affine.form().constant().negated(), only.getValue());
    }

    /** What the line drawn for the relation {@code key} settles, or null where none was. */
    private Settled drawnFor(String key, ModelOccurrence sole) {
        for (Cut cut : axes.get(axis).cuts()) {
            for (LineOrigin origin : cut.origins()) {
                if (!(origin instanceof LineOrigin.ComparisonOrigin guard)) {
                    continue;
                }
                boolean named = guard.part().isPresent()
                        && guard.part().get().part().relation().equals(key);
                boolean only = guard.part().isEmpty() && sole != null
                        && guard.read().states().equals(sole);
                if (!named && !only) {
                    continue;
                }
                InteractionCells.Cell cell = InteractionCells.sideOf(axes, axis, cut, guard, true);
                if (cell == null) {
                    return null;
                }
                if (only) {
                    soleLineOf = sole;
                }
                boolean[] yes = cell.allowed()[axis].clone();
                boolean[] no = new boolean[classes];
                for (int c = 0; c < classes; c++) {
                    no[c] = !yes[c];
                }
                return new Settled(yes, no);
            }
        }
        return null;
    }

    /** What the relations that were drawn say of the one that was not, by what implies what. */
    private Settled impliedFor(String key, Ray ray, Map<String, Ray> rays) {
        boolean[] yes = new boolean[classes];
        boolean[] no = new boolean[classes];
        for (String other : drawn) {
            Ray there = rays.get(other);
            if (there == null) {
                continue;
            }
            Settled settled = known.get(other);
            for (int c = 0; c < classes; c++) {
                if (settled.no()[c] && ray.implies(there)) {
                    no[c] = true;
                }
                if (settled.yes()[c] && there.implies(ray)) {
                    yes[c] = true;
                }
            }
        }
        return new Settled(yes, no);
    }

    /** What is known of {@code stated} on each class, or null where it is not a statement of
     *  relations. */
    Settled settled(Proposition stated) {
        switch (stated) {
            case Proposition.Always(boolean holds) -> {
                return new Settled(filled(holds), filled(!holds));
            }
            case Proposition.Compared leaf -> {
                Settled of = known.get(leaf.heldKey());
                if (of == null) {
                    return new Settled(filled(false), filled(false));
                }
                return leaf.holds() ? of : new Settled(of.no(), of.yes());
            }
            case Proposition.All all -> {
                boolean[] yes = filled(true);
                boolean[] no = filled(false);
                for (Proposition part : all.parts()) {
                    Settled one = settled(part);
                    if (one == null) {
                        return null;
                    }
                    for (int c = 0; c < classes; c++) {
                        yes[c] &= one.yes()[c];
                        no[c] |= one.no()[c];
                    }
                }
                return new Settled(yes, no);
            }
            case Proposition.Any any -> {
                boolean[] yes = filled(false);
                boolean[] no = filled(true);
                for (Proposition part : any.parts()) {
                    Settled one = settled(part);
                    if (one == null) {
                        return null;
                    }
                    for (int c = 0; c < classes; c++) {
                        yes[c] |= one.yes()[c];
                        no[c] &= one.no()[c];
                    }
                }
                return new Settled(yes, no);
            }
            default -> {
                return null;
            }
        }
    }

    /** Where {@code stated} holds, or null where some class is not settled. */
    Evaluated evaluate(Proposition stated) {
        Settled settled = settled(stated);
        if (settled == null) {
            return null;
        }
        for (int c = 0; c < classes; c++) {
            if (!settled.yes()[c] && !settled.no()[c]) {
                return null;
            }
        }
        return new Evaluated(settled.yes().clone(), explained());
    }

    /**
     * The classes a run can take the way an application of a closure comes out {@code held} in,
     * or null where some class is not settled: a class admits it where some application holds
     * (fails) throughout it, and not where every application fails (holds) throughout it.
     */
    Evaluated admittedBy(Collection<Proposition> applications, boolean held) {
        List<Settled> each = new ArrayList<>();
        for (Proposition application : applications) {
            Settled settled = settled(application);
            if (settled == null) {
                return null;
            }
            each.add(settled);
        }
        boolean[] admitted = new boolean[classes];
        for (int c = 0; c < classes; c++) {
            boolean some = false;
            boolean every = true;
            for (Settled one : each) {
                some |= held ? one.yes()[c] : one.no()[c];
                every &= held ? one.no()[c] : one.yes()[c];
            }
            if (!some && !every) {
                return null;
            }
            admitted[c] = some;
        }
        return new Evaluated(admitted, explained());
    }

    /** The comparisons of the model all of whose lines on this axis are relations drawn here. */
    private Set<ModelOccurrence> explained() {
        Map<ModelOccurrence, Boolean> every = new LinkedHashMap<>();
        for (Cut cut : axes.get(axis).cuts()) {
            for (LineOrigin origin : cut.origins()) {
                if (origin instanceof LineOrigin.ComparisonOrigin guard) {
                    boolean accounted = guard.part().isPresent()
                            ? drawn.contains(guard.part().get().part().relation())
                            : guard.read().states().equals(soleLineOf);
                    every.merge(guard.read().states(), accounted, Boolean::logicalAnd);
                }
            }
        }
        Set<ModelOccurrence> out = new LinkedHashSet<>();
        every.forEach((states, accounted) -> {
            if (accounted) {
                out.add(states);
            }
        });
        return out;
    }

    private boolean[] filled(boolean value) {
        boolean[] out = new boolean[classes];
        Arrays.fill(out, value);
        return out;
    }
}
