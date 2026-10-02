package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.Objects;

/**
 * How the values of a type are ordered: whether they are ordered at all, and by what.
 *
 * <p>These were two questions with one answer between them. Whether a type is ordered was a
 * {@code boolean}, and how to compare its values was worked out again at each of the four places
 * that emit a comparison — the operator, the sort family, the {@code sortBy} key, and the
 * {@code compareTo} a newtype carries. Four derivations of one fact disagree the way three did over
 * whether a {@code Date} is a carrier (see {@link Carrier}), and here the disagreement was silent:
 * {@code data StageN = Stage} was refused by {@code <} while its generated class declared
 * {@code Comparable<StageN>} and threw {@code IncompatibleClassChangeError} on the first Java reader
 * that compared two (issue #856).
 *
 * <p><b>Built from the spine, not from the base.</b> {@link TypeOps#base} answers what is left when
 * the names are off and drops how it got there, and a reader that then asks the next question of the
 * type as written is the defect this closes — it is what {@code BinaryElaborator} and the
 * {@code ORDERING} row of the old capability table both did, on the line after they computed the
 * base. So this keeps both halves of the spine's answer: its terminal ({@link
 * NewtypeInners#terminal}) says what the order is, and its first step ({@link TypeOps#outermost})
 * says whether a name is worn over it. Neither is read off the type as written.
 *
 * <p><b>Sealed, so an order added is one every reader has to answer for.</b> The switches over these
 * are what makes one more a build failure rather than a comparison emitted as an equality test.
 *
 * <p>The rules are ADR-0047 (a single-value newtype is compared by the value it wraps) and ADR-0069
 * (an enumeration is ordered by the order its cases are declared in, and that order lives on the sum
 * because one unit data may be a case of two sums). Composing them is what makes a newtype over an
 * enumeration ordered: {@code Ordered(Newtype<T>) = Ordered(T)} and {@code Ordered(Enumeration)},
 * so {@code Ordered(Newtype<Enumeration>)}.
 */
public sealed interface Ordering {

    /** A JVM {@code long}. {@code Int}, and nothing else. */
    record Longs() implements Ordering {}

    /**
     * The JVM value is {@link Comparable} and its {@code compareTo} is exactly the language's order:
     * a {@code BigDecimal}, a {@code Rational}, a {@code LocalDate}, a {@code LocalTime}, a
     * {@code LocalDateTime} or an {@code Instant} — and a single-value newtype as it is held, which
     * carries a {@code compareTo} of its own (ADR-0047).
     *
     * <p>Which way round that is matters. The language says what the order is and a carrier's
     * {@code compareTo} is used where it answers the same; being {@code Comparable} is not a reason
     * for a type to be here, which is why {@link Strings} is not.
     *
     * @param basis the type whose order this is: the primitive itself, or the one a newtype held as
     *              its own {@code Comparable} wraps
     */
    record Natural(Type basis) implements Ordering {

        public Natural {
            Objects.requireNonNull(basis, "a natural order is the order of some type");
        }
    }

    /**
     * Text, ordered by scalar value ({@code Strings.compare}). A {@code java.lang.String} is
     * {@link Comparable}, and its {@code compareTo} orders UTF-16 code units, which is another order
     * wherever a character past the basic plane meets one in {@code U+E000..U+FFFF}.
     */
    record Strings() implements Ordering {}

    /**
     * A value of an enumeration: the sum answers where a case stands in its declaration, through the
     * {@code __order} / {@code __ordering} it carries. The value itself is not {@code Comparable},
     * because one unit data may be a case of two sums that place it differently (ADR-0069).
     *
     * @param enumeration the sum whose declaration order this counts in
     */
    record Places(TypeSymbol enumeration) implements Ordering {}

    /**
     * A single-value newtype, which is two orders depending on what is on the stack: itself as the
     * JVM holds it, and {@code inner} once it has been opened to the value it wraps. Use
     * {@link #asHeld()} and {@link #opened()} rather than reading this apart.
     *
     * <p>Never nested. The order inside is read off the spine's terminal, and reading a terminal
     * takes no name off, so {@code Manager = Level = Int} is one {@code Wrapped(Longs)} and not two.
     */
    record Wrapped(Ordering inner) implements Ordering {

        public Wrapped {
            if (inner instanceof Wrapped) {
                throw new IllegalArgumentException(
                        "a wrapped order is read off the spine's terminal, so it is never wrapped again");
            }
        }
    }

    Ordering LONGS = new Longs();
    Ordering STRINGS = new Strings();

    /**
     * The type whose order this is, which is what the checker hands a backend in place of this: a
     * {@link Core.OrderingBasis}. What is a representation here — that an {@code Int} is a
     * {@code long}, that a newtype held as itself carries a {@code compareTo} — is left behind.
     */
    default Type basis() {
        return switch (this) {
            case Longs _ -> Type.INT;
            case Strings _ -> Type.STRING;
            case Natural natural -> natural.basis();
            case Places places -> Type.ref(places.enumeration());
            case Wrapped wrapped -> wrapped.inner().basis();
        };
    }

    /**
     * The sum that answers for the values of a sort over {@code subject}, or null where no
     * generated sum does: the class a sort over them names, for whatever asks which classes an
     * emitted call names.
     *
     * <p>Read off {@link #held}, which the emitter switches over, so the two cannot disagree about
     * which sort takes its comparator from a sum. A newtype over an enumeration answers null and
     * sorts by the {@code compareTo} its own class carries — the sum's {@code __order} would be
     * handed the wrapper and not the case.
     */
    static TypeSymbol enumerationOfHeld(Type subject, Core.OrderingBasis basis,
                                        DeclarationNewtypes newtypes) {
        return held(subject, basis, newtypes) instanceof Places places
                ? places.enumeration() : null;
    }

    /**
     * How the values of a sort over {@code subject} are ordered as the runtime is handed them,
     * given what the checker settled orders them. What the sort family reads, since it hands each
     * value over as it stands.
     *
     * <p>The basis says which order it is, and the subject says only whether a name is worn over the
     * value: a newtype is handed over as itself and by the {@code compareTo} its own class carries,
     * so it is {@link Natural} whatever the basis is. Nothing here asks what orders a type; that was
     * the checker's, and is on the call.
     *
     * <p>So it asks only whether the subject is a newtype, and nothing of what the newtype wraps: a
     * reader holding what it wraps would be a reader built against it.
     *
     * <p>Never {@link Wrapped}.
     */
    static Ordering held(Type subject, Core.OrderingBasis basis, DeclarationNewtypes newtypes) {
        return newtypes.wraps(subject) ? new Natural(basis.type()) : ofBasis(basis);
    }

    /**
     * How a value of this type, as the JVM holds it, is ordered — or null where it has no order.
     *
     * <p>Whether a type is ordered is this answer existing, and what orders it is the answer itself.
     * A reader that asks only whether a type is ordered has dropped what the checker then has to
     * put on the tree, so admission takes this answer and keeps it: a reader that admits a value it
     * cannot emit a comparison for is what #856 was.
     */
    static Ordering of(Type type, DeclarationAccess declarations) {
        return of(type, declarations.inners(), declarations.kinds(), declarations.published(),
                declarations.enumerations());
    }

    /**
     * The same, asking each question of the declarations where it is handed — for a reader that
     * holds its own answer to one of them.
     */
    static Ordering of(Type type, NewtypeInners inners, DeclarationKinds kinds,
                       PublishedDeclarations published, EnumerationListings listings) {
        Ordering terminal = ofBare(inners.terminal(type), kinds, published, listings);
        if (terminal == null) {
            return null;
        }
        // The spine has a layer exactly where its first step takes a name off.
        return TypeOps.outermost(type, inners) == null ? terminal : new Wrapped(terminal);
    }

    /**
     * How a value of the type a basis names is compared, once its names are off.
     *
     * <p>A translation and not a second resolution: it reads the basis and no declaration, so it
     * cannot answer differently from the checker that named it. A basis is the terminal of a
     * newtype spine and is never a newtype, and one that has no order — which the checker never
     * names — is a checker and an emitter disagreeing.
     */
    static Ordering ofBasis(Core.OrderingBasis basis) {
        Ordering how = switch (basis.type()) {
            case Type.Prim p -> ofPrimitive(p);
            case Type.Ref r -> new Places(r.name());
            default -> null;
        };
        if (how == null) {
            throw new IllegalStateException(
                    "an order the checker named is one that has none: " + Type.show(basis.type()));
        }
        return how;
    }

    /** The order of a primitive, or null where it has none. */
    private static Ordering ofPrimitive(Type.Prim p) {
        return switch (p) {
            case INT -> LONGS;
            case STRING -> STRINGS;
            // Each of these is carried by a Comparable whose compareTo is the order the language
            // gives it (spec §equality).
            case DECIMAL, DATE, TIME, DATETIME, INSTANT -> new Natural(p);
            // A Rational is ordered by its exact mathematical value (ADR-0116), and the runtime
            // value that carries one compares by exactly that — one representation per value, so
            // the order it carries and the equality it answers are the same reading of it.
            case RATIONAL -> new Natural(p);
            case BOOL -> null;
        };
    }

    /** How a value still held as the type it was asked of is ordered: a newtype by the {@code
     *  compareTo} its own class carries, everything else by itself. What the sort family reads,
     *  since it hands the value to the runtime as it stands. */
    default Ordering asHeld() {
        return this instanceof Wrapped ? new Natural(basis()) : this;
    }

    /** How a value is ordered once the newtype spine has been opened to its terminal value. What the
     *  operator reads, since it opens each operand before comparing. */
    default Ordering opened() {
        return this instanceof Wrapped w ? w.inner() : this;
    }

    /**
     * The order of a type with no newtype name left on it, or null where it has none. Every
     * constructor is answered, so a type constructor added to {@link Type} stops compiling until it
     * says whether it has an order.
     *
     * <p>Reads no name off: handed a newtype, it answers null, as it does for a product, and says
     * nothing about what the newtype wraps.
     */
    public static Ordering ofBare(Type terminal, DeclarationKinds kinds,
                                  PublishedDeclarations published, EnumerationListings listings) {
        return switch (terminal) {
            case Type.Prim p -> ofPrimitive(p);
            // A sum every one of whose cases is a unit data, one of its cases, or a union of them.
            // Null where more than one enumeration lists the case: the order belongs to the sum, so
            // a value two sums place differently has none of its own, and that is refused rather
            // than guessed (ADR-0069).
            case Type.Ref r -> placesIn(r, kinds, published, listings);
            case Type.Union u -> placesIn(u, kinds, published, listings);
            // A collection has no order of its own whatever it holds, a function and a tuple none at
            // all, and a type standing for a type has no values to order.
            case Type.ListOf _, Type.SetOf _, Type.OptionOf _, Type.MapOf _, Type.TupleOf _,
                 Type.FnOf _, Type.Open _, Type.Nothing _, Type.Never _, Type.Erroneous _ -> null;
        };
    }

    private static Ordering placesIn(Type t, DeclarationKinds kinds,
                                     PublishedDeclarations published,
                                     EnumerationListings listings) {
        TypeSymbol enumeration = TypeOps.orderingEnumeration(t, kinds, published, listings);
        return enumeration == null ? null : new Places(enumeration);
    }
}
