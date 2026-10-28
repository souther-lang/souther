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
        numbersIn(number, reads, origins);
        return origins.isEmpty() ? null : new BoundHeldIn(List.copyOf(origins), called);
    }

    private void numbersIn(Core number, InputReads reads, Set<Location> into) {
        switch (Core.withoutStanding(number)) {
            case Core.Binary binary -> {
                numbersIn(binary.left(), reads, into);
                numbersIn(binary.right(), reads, into);
            }
            case Core.Neg negated -> numbersIn(negated.operand(), reads, into);
            // A number is data where it is a field of one: a name alone is a value, and says
            // nothing of which table it is a number of.
            case Core.FieldAccess field -> into.addAll(originsOf(field, reads, new HashSet<>()));
            case Core.FieldProjection projection ->
                    into.addAll(originsOf(projection, reads, new HashSet<>()));
            default -> { }
        }
    }

    private Set<Location> originsOf(Core value, InputReads at, Set<BindingId> met) {
        return switch (Core.withoutStanding(value)) {
            case Core.Read name -> ofAName(name, at, met);
            case Core.FieldAccess field -> deeper(originsOf(field.target(), at, met),
                    field.target().type(), field.field());
            case Core.FieldProjection projection -> {
                Set<Location> out = originsOf(projection.base(), at, met);
                Type from = projection.base().type();
                for (Core.FieldProjection.Step each : projection.steps().inOrder()) {
                    out = deeper(out, from, each.field());
                    from = each.type();
                }
                yield out;
            }
            case Core.If choice -> union(originsOf(choice.then(), at, met),
                    originsOf(choice.els(), at, met));
            case Core.Match match -> {
                Set<Location> out = new LinkedHashSet<>();
                for (Core.Case each : match.cases()) {
                    out.addAll(originsOf(each.body(), at, met));
                }
                yield out;
            }
            case Core.IfConstructed construct -> {
                Set<Location> out = new LinkedHashSet<>(originsOf(construct.then(), at, met));
                for (Core.ElseArm each : construct.els()) {
                    out.addAll(originsOf(each.body(), at, met));
                }
                yield out;
            }
            case Core.LetIn let -> originsOf(let.body(), at, met);
            default -> Set.of();
        };
    }

    private Set<Location> ofAName(Core.Read name, InputReads at, Set<BindingId> met) {
        if (!met.add(name.binding())) {
            return Set.of(root(name));
        }
        // What a walk handed an element is the container the element came out of, and the step
        // into it: whichever table the fold ran over is the table, and the element's own field is
        // the column.
        List<Core> containers = at.containersTheElementCameFrom(name);
        if (!containers.isEmpty()) {
            Set<Location> out = new LinkedHashSet<>();
            for (Core container : containers) {
                for (Location each : originsOf(container, at, met)) {
                    out.add(new Location(each.root(), withElement(each.path())));
                }
            }
            return out;
        }
        if (at.meaningOf(name, read.rules().symbols(), read.rules().newtypes())
                instanceof ReadMeaning.Through through) {
            Core given = Core.withoutStanding(through.denotes().value());
            Set<Location> out = originsOf(given, through.denotes().at(), met);
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
