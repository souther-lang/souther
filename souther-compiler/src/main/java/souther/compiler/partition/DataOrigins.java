package souther.compiler.partition;

import souther.compiler.check.Location;
import souther.compiler.core.Core;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.ReadMeaning;
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
 * origin and is said so.
 *
 * <p>A name given a value that is no place — a literal, a call — is the root: it is the data, and
 * there is nothing further to follow. A value that names none is no origin, and a number with no
 * origin is told apart from nothing.
 */
final class DataOrigins {

    /** The step into an element of a container, which no field is spelled as. */
    private static final String ELEMENT = "[element]";

    private final InputReading read;

    /** What each root binding is called, for a reader; no part of which data it is. */
    private final Map<BindingId, String> called = new LinkedHashMap<>();

    DataOrigins(InputReading read) {
        this.read = read;
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
            case Core.Binary binary -> {
                numbersIn(binary.left(), reads, onPath, into);
                numbersIn(binary.right(), reads, onPath, into);
            }
            case Core.Neg negated -> numbersIn(negated.operand(), reads, onPath, into);
            case Core.FieldAccess field -> into.addAll(originsOf(field, reads, onPath));
            case Core.FieldProjection projection ->
                    into.addAll(originsOf(projection, reads, onPath));
            case Core.Read name -> {
                if (onPath.contains(name.binding())) {
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
            case Core.If choice -> {
                numbersIn(choice.then(), reads, onPath, into);
                numbersIn(choice.els(), reads, onPath, into);
            }
            default -> { }
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
            case Core.If choice -> union(originsOf(choice.then(), at, onPath),
                    originsOf(choice.els(), at, onPath));
            case Core.Match match -> {
                Set<Location> out = new LinkedHashSet<>();
                for (Core.Case each : match.cases()) {
                    out.addAll(originsOf(each.body(), at, onPath));
                }
                yield out;
            }
            case Core.IfConstructed construct -> {
                Set<Location> out = new LinkedHashSet<>(originsOf(construct.then(), at, onPath));
                for (Core.ElseArm each : construct.els()) {
                    out.addAll(originsOf(each.body(), at, onPath));
                }
                yield out;
            }
            case Core.LetIn let -> originsOf(let.body(), at, onPath);
            default -> Set.of();
        };
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

    private static Set<Location> union(Set<Location> one, Set<Location> other) {
        Set<Location> out = new LinkedHashSet<>(one);
        out.addAll(other);
        return out;
    }

    private static List<String> withElement(List<String> path) {
        List<String> out = new ArrayList<>(path);
        out.add(ELEMENT);
        return out;
    }
}
