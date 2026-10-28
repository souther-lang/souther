package souther.compiler.partition;

import souther.compiler.check.AffineForms;
import souther.compiler.check.Location;
import souther.compiler.check.ScopeStep;
import souther.compiler.core.Core;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.ReadMeaning;
import souther.compiler.meaning.Quantity;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Which data a number is read out of: the one place that decides it.
 *
 * <p>A number a comparison is held against is data when it is a field of something the model
 * holds — a table a helper was handed, a record a call was given — and what tells two such numbers
 * apart is the data, never the number. The data is a {@link Location}: the binding it is rooted at
 * and the fields read from there, which is how the rest of the compiler says where a value is.
 *
 * <p>What a name stands for is read from where it was given, however many names that takes: a
 * parameter of a helper is the argument it was handed, so the same table under another name, or
 * passed from two calls, is the root it was bound at and not the parameter of each call. A field
 * read off a value is the origin of the value with the field added, to any depth, so a record of
 * tables names each of them apart. What a walk handed an element is the container it took it from,
 * with a step into an element, so a column of a table is the table and its column. A value a
 * condition or a {@code match} chooses is one of the values its arms are, which is more than one
 * origin and is said so — unless an arm is no place, and then it is a value of its own.
 *
 * <p>What a number is made of is the arithmetic's to say ({@link AffineForms#partsOf}): an operator's
 * operands, an operation's declared arguments and the value a newtype wraps are followed, and
 * nothing else is. A name given a value that is no place — a literal, a call — is the root: it is
 * the data, and there is nothing further to follow. A value that names none is no origin, and a
 * number with no origin is told apart from nothing.
 */
final class DataOrigins {

    /** The step into an element of a container, which no field is spelled as. */
    private static final String ELEMENT = "[element]";

    private final InputReading read;

    /** The arithmetic a bound is read as a number by, which says what a number is made of. */
    private final AffineForms.Reading<Quantity, InputReads> arithmetic;

    /** The names whose numbers have been read, in the one bound this is asked of. */
    private final Set<BindingId> numbered = new HashSet<>();

    /** What each root binding is called, for a reader; no part of which data it is. */
    private final Map<BindingId, String> called = new LinkedHashMap<>();

    DataOrigins(InputReading read, AffineForms.Reading<Quantity, InputReads> arithmetic) {
        this.read = read;
        this.arithmetic = arithmetic;
    }

    /** The data the numbers of {@code number} are read out of, in {@code reads}, and none where it
     *  is read out of none. */
    BoundHeldIn ofTheNumbersIn(Core number, InputReads reads) {
        Set<Location> origins = new LinkedHashSet<>();
        numbersIn(number, reads, Set.of(), origins);
        return origins.isEmpty() ? null : new BoundHeldIn(List.copyOf(origins), called);
    }

    /**
     * A number is data where it is a field of some, or an element of a container. A name is what
     * it was given, so a number named by a {@code let} or handed to a helper is read out of what
     * it was made of, and a name given a literal is made of none.
     *
     * <p>{@code onPath} is the bindings this walk is inside of, which is what a cycle is. What
     * another branch of the walk met is no part of it.
     */
    private void numbersIn(Core number, InputReads reads, Set<BindingId> onPath,
                           Set<Location> into) {
        switch (Core.withoutStanding(number)) {
            case Core.FieldAccess field -> into.addAll(originsOf(field, reads, onPath));
            case Core.FieldProjection projection ->
                    into.addAll(originsOf(projection, reads, onPath));
            case Core.Read name -> {
                // Read once: what a name was made of is the same wherever it is read from, and a
                // value that names the same binding twice would otherwise be walked once for each
                // way down to it, which doubles with every name that names another twice.
                if (onPath.contains(name.binding()) || !numbered.add(name.binding())) {
                    return;
                }
                if (!reads.containersTheElementCameFrom(name).isEmpty()) {
                    into.addAll(originsOf(name, reads, onPath));
                } else if (reads.meaningOf(name, read.rules().symbols(), read.rules().newtypes())
                        instanceof ReadMeaning.Through through) {
                    numbersIn(through.denotes().value(), through.denotes().at(),
                            with(onPath, name.binding()), into);
                }
            }
            // What else a number is made of is the arithmetic's to say: the same parts it composes
            // the number out of, so an operation it reads a number through is one this reads the
            // data of.
            default -> {
                for (AffineForms.Part<InputReads> part
                        : AffineForms.partsOf(number, reads, arithmetic)) {
                    numbersIn(part.expression(), part.at(), onPath, into);
                }
            }
        }
    }

    private Set<Location> originsOf(Core value, InputReads at, Set<BindingId> onPath) {
        return switch (Core.withoutStanding(value)) {
            case Core.Read name -> ofAName(name, at, onPath);
            case Core.FieldAccess field -> deeper(originsOf(field.target(), at, onPath),
                    field.target().type(), field.field());
            case Core.FieldProjection projection -> {
                Set<Location> out = originsOf(projection.base(), at, onPath);
                Type from = projection.base().type();
                for (Core.FieldProjection.Step each : projection.steps().inOrder()) {
                    out = deeper(out, from, each.field());
                    from = each.type();
                }
                yield out;
            }
            // The value of a node that chooses or binds is what is in the children the scope steps
            // say are its answer, each read under the names in force there: the names a step goes
            // through are {@link ScopeStep}'s to say, and this keeps no list of its own.
            case Core.If _, Core.Match _, Core.IfConstructed _, Core.LetIn _ ->
                    answeredBy(Core.withoutStanding(value), at, onPath);
            default -> Set.of();
        };
    }

    /**
     * The origins of what {@code node} answers with: the body of a binding, or whichever arm a
     * condition chooses — all of theirs together, and none where any one of them has no place. A
     * value one arm of which is built where it stands, or computed, is a value of its own, and the
     * places of the others say only some of what it may be; the name it was given is then where the
     * data is.
     */
    private Set<Location> answeredBy(Core node, InputReads at, Set<BindingId> onPath) {
        List<Set<Location>> answers = new ArrayList<>();
        ScopeStep.forEachChild(node, (child, step) -> {
            if (step instanceof ScopeStep.Chosen || step instanceof ScopeStep.Let) {
                answers.add(originsOf(child, at.entering(step, read.rules().symbols(),
                        read.rules().newtypes()), onPath));
            }
        });
        Set<Location> out = new LinkedHashSet<>();
        for (Set<Location> each : answers) {
            if (each.isEmpty()) {
                return Set.of();
            }
            out.addAll(each);
        }
        return out;
    }

    /** {@code path} and {@code binding}: a walk that goes on from here has met it, and the walks
     *  beside this one have not. */
    private static Set<BindingId> with(Set<BindingId> path, BindingId binding) {
        Set<BindingId> out = new HashSet<>(path);
        out.add(binding);
        return out;
    }

    private Set<Location> ofAName(Core.Read name, InputReads at, Set<BindingId> before) {
        if (before.contains(name.binding())) {
            return Set.of(root(name));
        }
        Set<BindingId> onPath = with(before, name.binding());
        // What a walk handed an element is the container the element came out of, and the step
        // into it: whichever table the fold ran over is the table, and the element's own field is
        // the column.
        List<Core> containers = at.containersTheElementCameFrom(name);
        if (!containers.isEmpty()) {
            Set<Location> out = new LinkedHashSet<>();
            for (Core container : containers) {
                for (Location each : originsOf(container, at, onPath)) {
                    out.add(new Location(each.root(), withElement(each.path())));
                }
            }
            return out;
        }
        if (at.meaningOf(name, read.rules().symbols(), read.rules().newtypes())
                instanceof ReadMeaning.Through through) {
            Core given = Core.withoutStanding(through.denotes().value());
            Set<Location> out = originsOf(given, through.denotes().at(), onPath);
            if (!out.isEmpty()) {
                return out;
            }
        }
        // Given a value that is no place, or nothing: this is where the data is.
        return Set.of(root(name));
    }

    private Location root(Core.Read name) {
        called.putIfAbsent(name.binding(), name.name().replaceFirst("^\\$v\\d+_", ""));
        return Location.of(name.binding());
    }

    private Set<Location> deeper(Set<Location> of, Type readFrom, String field) {
        Set<Location> out = new LinkedHashSet<>();
        for (Location each : of) {
            out.add(each.then(readFrom, field, read.rules().newtypes()));
        }
        return out;
    }

    private static List<String> withElement(List<String> path) {
        List<String> out = new ArrayList<>(path);
        out.add(ELEMENT);
        return out;
    }
}
