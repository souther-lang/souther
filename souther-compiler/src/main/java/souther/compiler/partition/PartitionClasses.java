package souther.compiler.partition;

import souther.compiler.check.ReadingPolicy;
import souther.compiler.ast.Hir;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.TypeOps;
import souther.compiler.check.TypeView;
import souther.compiler.inputs.Case;
import souther.compiler.inputs.Distinctions;
import souther.compiler.inputs.Refinement;
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
    static List<PartitionClass> of(Type type, RuleReadingSource ruleSource, ReadingPolicy policy) {
        TypeView view = TypeView.of(type, ruleSource.symbols());
        return of(Distinctions.ofType(view, ruleSource.symbols()), view, ruleSource, policy);
    }

    /**
     * One class per distinction, in the order they were read.
     *
     * <p>A name the position wears that nothing here writes takes every class with it: the classes
     * are still the position's and a row already sitting in one still covers it, so what is absent
     * is the offer of a new row rather than the class.
     */
    static List<PartitionClass> of(List<Case> cases, TypeView view, RuleReadingSource ruleSource,
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
            if (!(ruleSource.symbols().scope().reach(each) instanceof TypeReachName.Written written)) {
                return unwritable(cases, view, ruleSource, policy, worn, each);
            }
            writes.add(written);
        }
        List<PartitionClass> out = new ArrayList<>();
        for (Case one : cases) {
            out.add(classOf(one, view, worn, policy, writes, ruleSource));
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
    private static List<PartitionClass> unwritable(List<Case> cases, TypeView view, RuleReadingSource ruleSource,
                                                   ReadingPolicy policy,
                                                   List<TypeSymbol> worn, TypeSymbol unnamed) {
        String why = notExposed(unnamed);
        List<PartitionClass> out = new ArrayList<>();
        // The classes of the same position with no names to write them under. What each is and what
        // reads a value into it are the position's either way; only the recipes are dropped, and
        // they are what there is no writing them.
        for (PartitionClass each : of(cases,
                new TypeView(view.declared(), List.of(), view.shape()), ruleSource, policy)) {
            out.add(PartitionClass.ungeneratable(each.id(), each.label(),
                    Recognition.Under.of(worn, each.recognises()), why)
                    .holding(each.denotes()).selecting(each.selects()));
        }
        return List.copyOf(out);
    }

    /** Why nothing here can write a value of {@code unnamed}: no spelling reaches it. */
    private static String notExposed(TypeSymbol unnamed) {
        return unnamed instanceof TypeSymbol.AtModule at
                ? "`" + at.module() + "` does not expose `" + at.name()
                        + "`, so nothing here can name it"
                // What the language declares is kept by nobody: a declaration of this module
                // spells it, so the language's has no name left here.
                : "`" + unnamed.name() + "` is declared here, so what the language declares under"
                        + " that name has no name here";
    }

    /** What a case's class is called, in one place: a reading that decides which cases the position
     *  holds names the same classes the reading above builds. */
    static String idOfCase(TypeSymbol leaf) {
        return leaf.name();
    }

    /**
     * The class one distinction gets, and the narrowing a row in it meets.
     *
     * <p>Exhaustive over {@link Case}, with no {@code default}: a distinction the reading learns to
     * make later stops this compiling rather than arriving as a class nothing can name.
     *
     * <p><b>Which narrowing it is is asked once, here, of the one reading that relates the two
     * vocabularies.</b> What a position divides into and what a position under it stands beneath are
     * the same statement read twice, and each arm below deciding for itself is how they came apart:
     * the arm for a sum's case spelled the narrowing again and the arm for an optional spelled none,
     * so an optional's classes narrowed nothing — a row could be asked to be `None` here and to hold
     * a class under `Some` at the same time, and nothing could say the two do not go together.
     */
    private static PartitionClass classOf(Case one, TypeView view, List<TypeSymbol> worn,
                                          ReadingPolicy policy,
                                          List<TypeReachName.Written> writes, RuleReadingSource ruleSource) {
        PartitionClass built = switch (one) {
            case Case.Truth truth -> eitherWay(truth.value(), worn, writes);
            case Case.Presence presence -> heldOrNot(presence.present(), view, worn, policy, writes, ruleSource);
            case Case.SumCase sum -> caseClass(sum, view.declared(), worn, policy, writes, ruleSource);
            case Case.Named named -> ValueClasses.classAt(named.value(), view, worn, ruleSource);
        };
        Refinement narrowing = Refinement.of(one);
        return narrowing == null ? built : built.selecting(narrowing);
    }

    /** One of the two values of a {@code Bool}, under the names the position writes it under. */
    private static PartitionClass eitherWay(boolean value, List<TypeSymbol> worn,
                                            List<TypeReachName.Written> writes) {
        // Each holds the one value it is named after, which is what lets a rule denying that value
        // be read as refusing the whole class.
        String said = Boolean.toString(value);
        return PartitionClass.of(said, said,
                        Recognition.Under.of(worn, new Recognition.Truth(value)),
                        RepresentativeSource.under(writes,
                                RepresentativeSource.of(FixtureTemplate.bool(value))))
                .holding(souther.compiler.values.ValueSet.just(
                        souther.compiler.values.Value.truth(value)));
    }

    /** Whether an optional holds anything, which is the one division its type makes. */
    private static PartitionClass heldOrNot(boolean present, TypeView view, List<TypeSymbol> worn,
                                            ReadingPolicy policy,
                                            List<TypeReachName.Written> writes, RuleReadingSource ruleSource) {
        if (!present) {
            return PartitionClass.of("None", "None",
                    Recognition.Under.of(worn, new Recognition.Held(false)),
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
        List<FixtureTemplate> some = Partitions.representativesOf(element, ruleSource, policy);
        Recognition is = Recognition.Under.of(worn, new Recognition.Held(true));
        return some.isEmpty()
                ? PartitionClass.ungeneratable("Some", "Some", is,
                        "nothing here composed a value of " + Type.show(element))
                : PartitionClass.of("Some", "Some", is,
                        RepresentativeSource.under(writes, RepresentativeSource.of(some)));
    }

    private static PartitionClass caseClass(Case.SumCase one, Type of, List<TypeSymbol> worn,
                                            ReadingPolicy policy,
                                            List<TypeReachName.Written> writes, RuleReadingSource ruleSource) {
        return holdingWhatItIs(one, writableCase(one.leaf(), of, worn, policy, writes, ruleSource));
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
    private static PartitionClass writableCase(TypeSymbol leaf, Type of, List<TypeSymbol> worn,
                                               ReadingPolicy policy,
                                               List<TypeReachName.Written> writes,
                                               RuleReadingSource ruleSource) {
        // Where the case sits on the position's order, decided here where the case, the position's
        // type and the declarations are all in hand. A line a body draws on an ordered enumeration
        // is at one of these places, and the class holding it is asked with the place.
        Recognition is = Recognition.Under.of(worn, new Recognition.OfCase(leaf,
                ValueClasses.placeOf(new souther.compiler.observe.ObservedValue.Unit(leaf), of,
                        ruleSource.symbols())));
        // A case whose module does not expose it: a value of the position all the same, and one no
        // author here can write down. Said as that, rather than offered under a spelling that
        // resolves to nothing wherever the row is pasted (issue #696).
        if (!(ruleSource.symbols().scope().reach(leaf) instanceof TypeReachName.Written names)) {
            return PartitionClass.ungeneratable(idOfCase(leaf), leaf.name(), is, notExposed(leaf));
        }
        // A case of a primitive-headed union is a primitive or one of the language's own, which
        // no module declares and nothing composes field by field: naming it builds it, the same as
        // a unit data. So the two are told apart here, where the declaration is asked for.
        if (!(leaf instanceof TypeSymbol.AtModule declared)
                || !(ruleSource.symbols().declaredNode(declared) instanceof Hir.Data data)) {
            return PartitionClass.of(idOfCase(leaf), leaf.name(), is,   // naming it builds it
                    RepresentativeSource.under(writes,
                            RepresentativeSource.of(FixtureTemplate.unitCase(names))));
        }
        if (data.newtype()) {
            List<FixtureTemplate> inner =
                    Partitions.insideTheNewtype(declared, ruleSource, policy);
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
                RepresentativeSource.under(writes, new RepresentativeSource.Composed(declared)));
    }

    private PartitionClasses() {}
}
