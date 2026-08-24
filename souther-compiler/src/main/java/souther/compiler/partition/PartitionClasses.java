package souther.compiler.partition;

import souther.compiler.check.ReadingPolicy;
import souther.compiler.ast.Hir;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeOps;
import souther.compiler.check.TypeView;
import souther.compiler.inputs.Case;
import souther.compiler.inputs.Distinctions;
import souther.compiler.inputs.Refinement;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeReachName;

import java.util.ArrayList;
import java.util.List;

/**
 * How a value of one distinction is named, recognised in a row, and written down.
 *
 * <p>Which distinctions a position has is not asked here. That is one reading, made once
 * ({@link Distinctions}, crossed with the rules where the position is read), and this is what the
 * partition adds to each of them — a name stable within its axis, a classifier for the rows an
 * author already wrote, and a recipe for a value standing for it.
 *
 * <p>Under the names the position wears, because that is how a row writes the value. The names come
 * off to say what the position is and go back on to say what stands at it.
 */
final class PartitionClasses {

    /** The classes a type states, before any rule is crossed with them. What a witness varies over
     *  and what a generator offers for a bare position, which are asked of a type and not of a
     *  position of one. */
    static List<PartitionClass> of(Type type, Symbols symbols, ReadingPolicy policy) {
        TypeView view = TypeView.of(type, symbols);
        return of(Distinctions.ofType(view, symbols), view, symbols, policy);
    }

    /**
     * One class per distinction, in the order they were read.
     *
     * <p>A name the position wears that nothing here writes takes every class with it: the classes
     * are still the position's and a row already sitting in one still covers it, so what is absent
     * is the offer of a new row rather than the class.
     */
    static List<PartitionClass> of(List<Case> cases, TypeView view, Symbols symbols,
                                   ReadingPolicy policy) {
        if (cases.isEmpty()) {
            return List.of();
        }
        List<TypeSymbol> worn = view.wrappers().stream().map(TypeOps.Layer::named).toList();
        // The same names twice over, because two different questions are asked of them. Whether an
        // observed value is under this class is asked of the declarations, and what a row writes it
        // under is asked of the module doing the writing — one of these is an identity and the other
        // is a reference, and a module reaching a name through an alias answers them differently.
        List<TypeReachName.Written> writes = new ArrayList<>();
        for (TypeSymbol each : worn) {
            if (!(symbols.scope().reach(each) instanceof TypeReachName.Written written)) {
                return unwritable(cases, view, symbols, policy, worn, each);
            }
            writes.add(written);
        }
        List<PartitionClass> out = new ArrayList<>();
        for (Case one : cases) {
            out.add(classOf(one, view, worn, policy, writes, symbols));
        }
        return List.copyOf(out);
    }

    /**
     * The classes of a position whose values cannot be written here at all, each saying why.
     *
     * <p>They are counted like any other: a case a module does not expose is still a case of the
     * position, and a row already sitting in one still covers it. What is absent is the offer of a
     * new row, and the reason is the model's — {@code domain} keeps the case to itself — rather than
     * anything about this generator.
     */
    private static List<PartitionClass> unwritable(List<Case> cases, TypeView view, Symbols symbols,
                                                   ReadingPolicy policy,
                                                   List<TypeSymbol> worn, TypeSymbol unnamed) {
        String why = notExposed(unnamed);
        List<PartitionClass> out = new ArrayList<>();
        // The classes of the same position with no names to write them under. What each is and what
        // reads a value into it are the position's either way; only the recipes are dropped, and
        // they are what there is no writing them.
        for (PartitionClass each : of(cases,
                new TypeView(view.declared(), List.of(), view.shape()), symbols, policy)) {
            out.add(PartitionClass.ungeneratable(each.id(), each.label(),
                    Classifier.under(worn, each.classifier()), why)
                    .holding(each.denotes()).selecting(each.selects()));
        }
        return List.copyOf(out);
    }

    /** Why nothing here can write a value of {@code unnamed}: no spelling reaches it. */
    private static String notExposed(TypeSymbol unnamed) {
        return "`" + unnamed.module() + "` does not expose `" + unnamed.name()
                + "`, so nothing here can name it";
    }

    /** What a case's class is called, in one place: a reading that decides which cases the position
     *  holds names the same classes the reading above builds. */
    static String idOfCase(TypeSymbol leaf) {
        return leaf.name();
    }

    /**
     * The class one distinction gets.
     *
     * <p>Exhaustive over {@link Case}, with no {@code default}: a distinction the reading learns to
     * make later stops this compiling rather than arriving as a class nothing can name.
     */
    private static PartitionClass classOf(Case one, TypeView view, List<TypeSymbol> worn,
                                          ReadingPolicy policy,
                                          List<TypeReachName.Written> writes, Symbols symbols) {
        return switch (one) {
            case Case.Truth truth -> eitherWay(truth.value(), worn, writes);
            case Case.Presence presence -> heldOrNot(presence.present(), view, worn, policy, writes, symbols);
            case Case.SumCase sum -> caseClass(sum, worn, policy, writes, symbols);
            case Case.Named named -> ValueClasses.classAt(named.value(), view, worn, symbols);
        };
    }

    /** One of the two values of a {@code Bool}, under the names the position writes it under. */
    private static PartitionClass eitherWay(boolean value, List<TypeSymbol> worn,
                                            List<TypeReachName.Written> writes) {
        // Each holds the one value it is named after, which is what lets a rule denying that value
        // be read as refusing the whole class.
        String said = Boolean.toString(value);
        return PartitionClass.of(said, said,
                        Classifier.under(worn, Classifier.byShape(v -> isBool(v, value))),
                        RepresentativeSource.under(writes,
                                RepresentativeSource.of(FixtureTemplate.bool(value))))
                .holding(souther.compiler.values.ValueSet.just(
                        souther.compiler.values.Value.truth(value)));
    }

    /** Whether an optional holds anything, which is the one division its type makes. */
    private static PartitionClass heldOrNot(boolean present, TypeView view, List<TypeSymbol> worn,
                                            ReadingPolicy policy,
                                            List<TypeReachName.Written> writes, Symbols symbols) {
        if (!present) {
            return PartitionClass.of("None", "None",
                    Classifier.under(worn,
                            Classifier.byShape(v -> v instanceof ObservedValue.Absent)),
                    RepresentativeSource.under(writes,
                            RepresentativeSource.of(FixtureTemplate.none())));
        }
        if (!(view.shape() instanceof souther.compiler.check.Shape.Optional optional)) {
            // The reading states whether an optional holds anything only of an optional. A class
            // for one anywhere else is the two readings of a position disagreeing about its shape.
            throw new IllegalStateException(
                    "`" + Type.show(view.declared()) + "` is asked whether it holds a value, and it"
                            + " is not an optional; the reading of a position and the classes built"
                            + " from it disagree about its shape");
        }
        Type element = optional.element();
        List<FixtureTemplate> some = Partitions.representativesOf(element, symbols, policy);
        Classifier is = Classifier.under(worn,
                Classifier.byShape(v -> !(v instanceof ObservedValue.Absent)));
        return some.isEmpty()
                ? PartitionClass.ungeneratable("Some", "Some", is,
                        "nothing here composed a value of " + Type.show(element))
                : PartitionClass.of("Some", "Some", is,
                        RepresentativeSource.under(writes, RepresentativeSource.of(some)));
    }

    private static PartitionClass caseClass(Case.SumCase one, List<TypeSymbol> worn,
                                            ReadingPolicy policy,
                                            List<TypeReachName.Written> writes, Symbols symbols) {
        // The narrowing a row in this class meets, carried from the distinction it was made from. A
        // row whose value here is an `Approved` is a row at every position the `Approved` case
        // declares, and that is the same fact read from the other end.
        return holdingWhatItIs(one, writableCase(one.leaf(), worn, policy, writes, symbols))
                .selecting(new Refinement.SumCase(one.leaf()));
    }

    /**
     * The same class, saying which values it holds.
     *
     * <p>Said of the distinction and not of the class that came back, because what a class means and
     * whether a row for it can be written down are two answers and only the second turns on which
     * module is reading. A case another module keeps to itself took the arm that says nothing can be
     * written for it and left without saying what it holds — so a rule denying that case had nothing
     * to prove itself against, and the case stayed in the denominator of every module but the one
     * that declared it.
     */
    private static PartitionClass holdingWhatItIs(Case.SumCase one, PartitionClass built) {
        return one.denotes() == null ? built : built.holding(one.denotes());
    }

    /** The class itself: what it is called, what it recognises, and what can be written for it. */
    private static PartitionClass writableCase(TypeSymbol leaf, List<TypeSymbol> worn,
                                               ReadingPolicy policy,
                                               List<TypeReachName.Written> writes,
                                               Symbols symbols) {
        Classifier is = Classifier.under(worn, Classifier.byShape(v -> switch (v) {
            case ObservedValue.Unit u -> leaf.equals(u.type());
            case ObservedValue.Constructed c -> leaf.equals(c.type());
            default -> false;
        }));
        // A case whose module does not expose it: a value of the position all the same, and one no
        // author here can write down. Said as that, rather than offered under a spelling that
        // resolves to nothing wherever the row is pasted (issue #696).
        if (!(symbols.scope().reach(leaf) instanceof TypeReachName.Written names)) {
            return PartitionClass.ungeneratable(idOfCase(leaf), leaf.name(), is, notExposed(leaf));
        }
        if (!(symbols.declarations().declaration(leaf.key()) instanceof Hir.Data data)) {
            return PartitionClass.of(idOfCase(leaf), leaf.name(), is,   // naming it builds it
                    RepresentativeSource.under(writes,
                            RepresentativeSource.of(FixtureTemplate.unitCase(names))));
        }
        if (data.newtype()) {
            List<FixtureTemplate> inner = Partitions.insideTheNewtype(leaf, symbols, policy);
            return inner.isEmpty()
                    ? PartitionClass.ungeneratable(idOfCase(leaf), leaf.name(), is,
                            "nothing here composed a value of what `" + leaf.name() + "` wraps")
                    : PartitionClass.of(idOfCase(leaf), leaf.name(), is,
                            RepresentativeSource.under(writes, RepresentativeSource.under(
                                    List.of(names), RepresentativeSource.of(inner))));
        }
        // A record case is written field by field, which is the generator's composition. So the class
        // names the constructor and the generator does the composing — the same walk every other
        // record goes through, rules between the fields and all. Under the position's names either
        // way: what is composed is an `Approved`, and what the row writes is `DecisionN(Approved
        // { id = 1 })`.
        return PartitionClass.of(idOfCase(leaf), leaf.name(), is,
                RepresentativeSource.under(writes, new RepresentativeSource.Composed(leaf)));
    }

    private static boolean isBool(ObservedValue v, boolean expected) {
        return v instanceof ObservedValue.Bool b && b.value() == expected;
    }

    private PartitionClasses() {}
}
