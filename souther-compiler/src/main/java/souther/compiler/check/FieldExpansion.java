package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.SequencedMap;
import java.util.Set;

/**
 * What a declaration reaches through its spreads, as the structure it is.
 *
 * <p>Every question about the fields of a product is answered from this: which type stands at each
 * name, which binding each name is, and the order a value lays them out in. Those are three
 * different relations over one graph, and each was its own walk — so the order one of them reached
 * a field in was the order another one was read in, and a walk that stopped where the others did
 * not was a difference nothing had a name for.
 *
 * <p><b>Topology, and no reading of it.</b> What comes back says which declaration was reached
 * through which spread, and holds each declaration's own fields as it wrote them. It states no
 * order over the whole closure, because there is more than one and they are not the same: a value
 * lays out what it spreads before what it writes, and a name written on a declaration means that
 * declaration's field rather than the one a spread brought in. A reader takes the one it means.
 *
 * <p><b>Total over a cyclic graph.</b> A spread reaching a declaration already being expanded is a
 * back edge and is handed back as one rather than followed, so that the expansion of any graph is
 * finite. What a back edge means is not decided here: a declaration that spreads itself is refused
 * before anything reads what one of them holds ({@link ProductSpreads}), and a reader that answers
 * about a program mid-edit has an answer to give either way.
 *
 * <p><b>A declaration reached twice down two spreads is expanded twice.</b> Which is not a cost
 * being overlooked but the thing being asked: the two fields it brings in are two fields with one
 * name, and a walk that remembered the declaration across branches would answer as though one of
 * them had never been written. Whether that is refused or folded is the reader's, and both readers
 * exist.
 */
public final class FieldExpansion {

    private FieldExpansion() {}

    /**
     * Where a declaration is read from.
     *
     * <p>The one thing the two worlds differ by. A compilation asks the store, which records that
     * the answer it is building depends on the declaration it read; a pass holding a scope asks
     * that. What a spread reaches, which declaration binds a field it brought in, and where a back
     * edge is are decided here either way.
     */
    @FunctionalInterface
    public interface Declarations {

        /** The declaration at {@code named} with its names resolved, or null where none is. */
        Hir.Def at(TypeSymbol.AtModule named);
    }

    /**
     * One declaration as a reader of its fields reaches it.
     *
     * @param declares the name this declaration was reached by, which is what binds its own fields
     * @param declaration what was written under that name, which is what a report about one of its
     *     fields names
     * @param includes what it spreads, in the order they are written
     */
    public record Of(TypeSymbol.AtModule declares, Hir.Data declaration, List<Include> includes) {

        public Of {
            includes = List.copyOf(includes);
        }

        /** The fields written on it, in the order they are written. */
        public List<Hir.Field> ownFields() {
            return declaration.fields();
        }
    }

    /**
     * One spread written on a declaration, and what it reached.
     *
     * <p>Four arms because a reader has four things to say. Three of them bring in no field, and
     * which of the three it is decides what a reader may report about it — a name nothing declares
     * was already reported where it is written, a name declaring something that is not a product is
     * the author spreading the wrong thing, and a back edge is a declaration that contains itself.
     */
    public sealed interface Include {

        /** The spread as it is written, which is where a report about it goes. */
        Hir.Name written();

        /** A spread of a product, with what it reaches. */
        record Expanded(Hir.Name written, Of target) implements Include {}

        /** A spread reaching a declaration the expansion it is part of is already inside. */
        record BackEdge(Hir.Name written, TypeSymbol.AtModule target) implements Include {}

        /** A spread of a name nothing declares. */
        record NamesNothing(Hir.Name written) implements Include {}

        /** A spread of a name declaring something no field can be taken out of. */
        record NotAProduct(Hir.Name written, TypeSymbol target) implements Include {}
    }

    /**
     * What {@code data}, reached as {@code declared}, spreads and writes.
     *
     * <p>{@code declared} is the name the caller reached the declaration by, and is the caller's to
     * name: a declaration carries the name it was written under rather than the module reading it,
     * so a binding worked out from whoever is asking would be a different binding for the same
     * field, and the clauses carried in with the declaration would resolve against nothing.
     */
    public static Of of(TypeSymbol.AtModule declared, Hir.Data data, Declarations declarations) {
        return expand(declared, data, declarations, new LinkedHashSet<>());
    }

    /**
     * {@code onThePath} is what is being expanded above this, and is what makes the walk finite. It
     * is the path and not everything reached: a declaration two spreads reach is reached twice, and
     * one that reaches itself is reached once and handed back as a back edge.
     */
    private static Of expand(TypeSymbol.AtModule declared, Hir.Data data,
                             Declarations declarations, Set<TypeSymbol.AtModule> onThePath) {
        onThePath.add(declared);
        List<Include> includes = new ArrayList<>();
        for (Hir.Name written : data.includes()) {
            includes.add(reached(written, declarations, onThePath));
        }
        onThePath.remove(declared);
        return new Of(declared, data, includes);
    }

    private static Include reached(Hir.Name written, Declarations declarations,
                                   Set<TypeSymbol.AtModule> onThePath) {
        if (!(written instanceof Hir.Name.Denoting denoting)) {
            return new Include.NamesNothing(written);
        }
        TypeSymbol denotes = denoting.type();
        if (!(denotes instanceof TypeSymbol.AtModule at)) {
            // What the language gives is no declaration to walk. A spread of one takes in no field
            // and is the author spreading something a value is not made of.
            return new Include.NotAProduct(written, denotes);
        }
        if (onThePath.contains(at)) {
            return new Include.BackEdge(written, at);
        }
        Hir.Def found = declarations.at(at);
        if (found instanceof Hir.Data data) {
            return new Include.Expanded(written, expand(at, data, declarations, onThePath));
        }
        return found == null ? new Include.NamesNothing(written)
                : new Include.NotAProduct(written, at);
    }

    /**
     * What put a field where a declaration reaches it — one of its own, or one of its spreads.
     *
     * <p>Of the declaration being expanded and not of the one that wrote the field. Where two of
     * the fields a declaration reaches carry one name, what an author is shown is which two of
     * <em>its</em> spreads brought them: a declaration further down that both of them reach is one
     * neither of them wrote, and the two fields met there rather than here.
     */
    public sealed interface Supplier {

        /** A field written on the declaration itself. */
        record Own(Hir.Field field) implements Supplier {}

        /** A field a spread written on the declaration brought in. */
        record Spread(Hir.Name written) implements Supplier {}
    }

    /**
     * What a reader of the fields says about a declaration that does not hold together.
     *
     * <p>Beside the projection rather than inside it. What the fields of a declaration are is one
     * question and what is said about a declaration that reaches two of them under one name is
     * another, and the two have different answers in the two places this is read from: the pass
     * that holds a declaration to its rules refuses it, and a compilation answering about a program
     * being edited has an answer to give for whatever is written at the moment.
     */
    public interface Refusing {

        /** Nothing is said, for a reader that answers about whatever is written. */
        Refusing NOTHING = new Refusing() {
            @Override
            public void twice(String field, Of of, Supplier arriving, Supplier held) {
                // Folded rather than refused: the field keeps the place the first of them gave it
                // and the type the last of them wrote, which is an answer and is the same answer
                // however often it is asked.
            }

            @Override
            public void notAProduct(Include.NotAProduct include) {
                // Brings in no field, which is all a reader of the fields needs of it.
            }
        };

        /**
         * Two of the fields {@code of} reaches carry one name: {@code arriving} supplies the one
         * being taken in, and {@code held} the one already there.
         */
        void twice(String field, Of of, Supplier arriving, Supplier held);

        /** A spread naming something no field can be taken out of. */
        void notAProduct(Include.NotAProduct include);
    }

    /** One field as a declaration reaches it: what is in it, and what put it there. */
    private record Held(Type type, Supplier by) {}

    /**
     * What each field the expansion reaches holds.
     *
     * <p><b>A mapping.</b> What comes back iterates, as something has to, and in what order it does
     * is not answered here — {@link #layout} is, and is not read off this. Held apart because a
     * reader of one has no business being worked out again by an edit to the other, which is the
     * whole of why these are projections rather than one answer with two things in it.
     *
     * <p>A name reached twice takes the type the last of them wrote. Which is the answer for a
     * reader that answers about whatever is written; {@code refusing} is what the pass that holds a
     * declaration to its rules says instead.
     */
    public static Map<String, Type> types(Of of, Refusing refusing) {
        Map<String, Type> out = new LinkedHashMap<>();
        held(of, refusing).forEach((name, held) -> out.put(name, held.type()));
        return out;
    }

    /**
     * The order a value of the declaration lays its fields out in: what each spread brings in,
     * spread by spread as they are written, and then what the declaration writes itself.
     *
     * <p><b>A sequence, and it is the whole of what this says.</b> Read off the expansion beside
     * {@link #types} rather than out of it: a projection taken from another is that other one, and
     * a reader of the order would be reading a mapping again the day either of them moved.
     *
     * <p>A name reached twice stands where the first of them put it.
     */
    public static List<String> layout(Of of, Refusing refusing) {
        return List.copyOf(held(of, refusing).keySet());
    }

    /**
     * The expansion merged declaration by declaration: what each field holds and what put it there,
     * in the order a value lays them out.
     *
     * <p>Private, and the one thing the projections above share. What each of them answers is a
     * narrowing of this, and none of them is a narrowing of another — so nothing outside can take
     * an order off a mapping or a type off a sequence, whatever this happens to be carried in.
     *
     * <p><b>Closed at each declaration.</b> The fields a spread brings in are worked out from that
     * declaration's own expansion before any of them is taken in here, so two fields that met
     * further down met there, and what is said about them names the spreads of the declaration
     * they met under.
     */
    private static SequencedMap<String, Held> held(Of of, Refusing refusing) {
        SequencedMap<String, Held> out = new LinkedHashMap<>();
        for (Include include : of.includes()) {
            switch (include) {
                case Include.Expanded(Hir.Name written, Of target) -> {
                    Supplier by = new Supplier.Spread(written);
                    held(target, refusing).forEach(
                            (name, held) -> take(out, name, held.type(), by, of, refusing));
                }
                case Include.NotAProduct bad -> refusing.notAProduct(bad);
                // A name nothing declares is reported where it is written, and a spread folding
                // back onto a declaration being expanded brings in what that declaration already
                // reaches. Neither adds a field here.
                case Include.NamesNothing _, Include.BackEdge _ -> { }
            }
        }
        for (Hir.Field field : of.ownFields()) {
            take(out, field.name(), TypeOps.fieldType(field), new Supplier.Own(field), of, refusing);
        }
        return out;
    }

    private static void take(SequencedMap<String, Held> out, String name, Type type, Supplier by,
                             Of of, Refusing refusing) {
        Held had = out.get(name);
        if (had != null) {
            refusing.twice(name, of, by, had.by());
        }
        // Put and not putIfAbsent: a name already here keeps the place it was given and takes the
        // type of the one arriving, which is what a declaration's own field does to one a spread
        // brought in.
        out.put(name, new Held(type, by));
    }

    /**
     * Which binding each field the expansion reaches is: the declaration's own fields, numbered as
     * it writes them, and then what its spreads bring in, each keeping the binding of the
     * declaration that wrote it.
     *
     * <p><b>Its own first, and the first binding for a name is the one kept.</b> Not the order a
     * value lays its fields out in, and not a second reading of it: which field a name means is
     * decided by the declaration the clause reading it was written on, so a declaration's own field
     * means its own wherever a spread brought another of that name in. The two relations are over
     * one graph and are not each other, which is why this reads the expansion rather than the
     * sequence beside it.
     *
     * <p>Nothing is refused here. A name reached twice has an answer — the nearer one — and the
     * declaration that reaches two of them is refused where its fields are worked out.
     */
    public static Map<String, BindingId> bindings(Of of) {
        Map<String, BindingId> out = new LinkedHashMap<>();
        bind(of, out);
        return out;
    }

    private static void bind(Of of, Map<String, BindingId> out) {
        BindingOwner owner = new BindingOwner.OfFields(of.declares());
        int ordinal = 0;
        for (Hir.Field field : of.ownFields()) {
            out.putIfAbsent(field.name(), new BindingId(owner, ordinal++));
        }
        for (Include include : of.includes()) {
            if (include instanceof Include.Expanded(Hir.Name _, Of target)) {
                bind(target, out);
            }
        }
    }
}
