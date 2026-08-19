package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.types.CoverageOrigin;
import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.NumericDomain.LinearForm;
import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BindingId;
import souther.compiler.types.ConstructionOrigin;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ReachName;
import souther.compiler.types.ValueName;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * What a value is to the invariant-discharge check: where it is, what it is called, and whether
 * anything can be said of it.
 *
 * <p>One question asked in one place. A guard states something of a value and a clause is read
 * against a value, and the two meet only by being named alike — so the naming is here rather than at
 * either end of it, and asking it of a name gives the same answer as asking it of the expression the
 * name was bound to. That is what makes naming an expression not change what is known of it.
 *
 * <p>Three answers, and they are not the same question. Where a value is, is a {@link Location} and
 * is what the seeding writes about. What a value is called, is a key: two expressions with one key
 * compute one value, which is the whole of what the fact set knows. What can be said of a value, is
 * whether a clause read against it could ever be discharged — a location always can, and so does a
 * number this grammar names, whatever computes it; a value of another kind only where a rule or a
 * guard reaches it — and it is what decides whether a construction is reported at all.
 *
 * <p>The middle question does not wait on the third. A value is called something because it can be
 * pointed at, and what is known of it is a separate matter that may well be nothing. Deciding the
 * one by the other is circular where it matters most: the first guard about a value would be read
 * under a naming that guard is what establishes.
 */
final class Terms {

    private final Symbols symbols;
    private final Map<TypeSymbol, java.util.Optional<Type>> affineScalarBases = new HashMap<>();
    /** How the values of each atom this has named are spaced. Kept here because this is where an
     * atom's name is made: the key and the kind of number behind it are decided in one step, and
     * anywhere else would be a second place that has to agree about which is which. */
    private final Map<FactSubject, Granularity> atomKinds = new HashMap<>();
    /**
     * The terms this reading has built, each held under the one instance standing for it.
     *
     * <p>What a term is made of is a graph and not a tree: a name read twice is one value read twice,
     * and {@code let (a, b) = t} reads {@code t} twice by itself. A term holds its parts rather than
     * a copy of them, and carries the hash they were hashed into, so a chain of them costs a link per
     * link. Sharing is what makes the comparison stop at the first line; it is not what makes two
     * terms equal ({@link Term}).
     */
    private final Term.Interner interned = new Term.Interner();
    /** How each atom outside the affine fragment was computed. */
    private final Map<FactSubject, Derivation> derivations = new HashMap<>();

    /** The subject each evaluation this could not name is, made once per occurrence. Identity-keyed:
     * an occurrence is a node, and two nodes are two evaluations however alike they are written. */
    private final java.util.IdentityHashMap<Core, EvaluationId> evaluations =
            new java.util.IdentityHashMap<>();

    /** What each node a rewrite built stands for, so an occurrence keeps its identity through one. */
    private final java.util.IdentityHashMap<Core, Core> builtFrom = new java.util.IdentityHashMap<>();

    /** What each atom this named outside the affine fragment was computed from. */
    Map<FactSubject, Derivation> derivations() {
        return derivations;
    }

    Terms(Symbols symbols) {
        this(symbols, Of.THE_DISCHARGE_TREE);
    }

    Terms(Symbols symbols, Of reading) {
        this.symbols = symbols;
        this.reading = reading;
    }

    /**
     * Which tree a reading is over, which decides whether a shape with no term says anything about
     * this compiler.
     *
     * <p>The discharge reader is handed a tree where the language's own operations are still
     * operations, so a shape it has no term for is a shape nothing here has got round to. The tree
     * that runs has those operations expanded into the folds they are, and meeting one of those is
     * the representation rather than a gap — recorded as a gap it would say this compiler cannot
     * name {@code List.map} when what it cannot name is a fold nobody wrote.
     */
    enum Of {
        /** The tree the invariant-discharge analysis reads. */
        THE_DISCHARGE_TREE,
        /** The tree the backend emits, which every measure is taken over. */
        THE_TREE_THAT_RUNS
    }

    private final Of reading;

    /**
     * Where a test in this package reads the shapes this had no term for, and null everywhere else.
     *
     * <p>Beside {@link InvariantChecker#WATCHING} and for the same reason. A shape with no term is
     * silent, and silence is what a value nothing can be said of produces as well — so the difference
     * between this compiler being unfinished and a value being unnameable has nowhere else to be
     * read, and a difference nothing can read stops being true without anything failing.
     */
    static List<String> UNSUPPORTED;

    /** The operator {@code e} is, where it is a library call written as a function, or {@code e}
     * itself. Reading it as the operator is what puts it on the one path the operator already has,
     * rather than on a second path that would have to be kept saying the same thing. */
    static Core asOperator(Core e) {
        if (e instanceof Core.PreservedCall call && call.args().size() == 2) {
            Hir.BinOp op = DischargeRules.operator(call.operation());
            if (op != null) {
                // Not a comparison any source wrote: a preserved call read as the operator it
                // stands for. This tree is the discharge reader's, never the tree that runs.
                return new Core.Binary(op, call.args().get(0), call.args().get(1),
                        CoverageOrigin.unwritten(), call.type(), call.pos());
            }
        }
        return e;
    }

    /**
     * The affine walk: literals and {@code +}/{@code -} compose; every other node is handed to
     * {@code leaf} (which decides whether it is an atom, a location, or opaque). It takes the leaf
     * rule rather than fixing one because a binding it reads through answers with what that binding
     * was given.
     *
     * <p>A node this has a rule for and cannot compose is handed to {@code leaf} as well. Reading the
     * structure of a value and naming the value are two questions: a variable product is outside the
     * fragment, and it is still one value, so what a guard states of it is still about the thing the
     * clause reads. Answering the first question with {@code null} and never asking the second is
     * what made {@code a * b} name nothing where it is written and something where it is bound —
     * which is a name changing what can be said of an expression.
     */
    LinearForm<FactSubject> affine(Core raw, Denotations at, java.util.function.Function<Core, LinearForm<FactSubject>> leaf) {
        Core e = asOperator(raw);
        if (e instanceof Core.PreservedCall) {
            // A call that folds is the number it folds to. `String.length("1A")` is 2, and a clause
            // about it is decided rather than owed — the run-time check is not what should answer a
            // question the compiler has already computed. Asked once: folding walks the subtree, and
            // a pattern in it is a regex to run.
            BigDecimal folded = constantNumber(e);
            if (folded != null) {
                return LinearForm.constant(folded);
            }
        }
        LinearForm<FactSubject> composed = composed(e, at, leaf);
        return composed != null ? composed : leaf.apply(e);
    }

    /** {@code e} read as arithmetic over what {@code leaf} answers, or {@code null} where this has no
     * rule for it or the rule it has does not compose. */
    private LinearForm<FactSubject> composed(Core e, Denotations at,
                                java.util.function.Function<Core, LinearForm<FactSubject>> leaf) {
        return switch (e) {
            case Core.Int i -> LinearForm.constant(BigDecimal.valueOf(i.value()));
            case Core.Decimal d -> LinearForm.constant(d.value());
            case Core.Neg n -> negate(affine(n.operand(), at, leaf));
            case Core.Binary b when b.op() == Hir.BinOp.ADD ->
                    add(affine(b.left(), at, leaf), affine(b.right(), at, leaf), false);
            case Core.Binary b when b.op() == Hir.BinOp.SUB ->
                    add(affine(b.left(), at, leaf), affine(b.right(), at, leaf), true);
            // scalar multiply by a constant (Amount * 2) is linear; `/` and a variable product are not
            // (a divide truncates for Int, and a variable factor is non-linear), so those come back
            // here as one value rather than as arithmetic over two.
            case Core.Binary b when b.op() == Hir.BinOp.MUL ->
                    scale(affine(b.left(), at, leaf), affine(b.right(), at, leaf));
            // A newtype's `.value` read off something that is not a place: what it wraps is what it
            // is, which is the rule a location is keyed by ({@link #pathKey}) read of a computed
            // value too. Without it `f(x).value` is one value where the same call given a name is
            // the arithmetic its body wrote — a name deciding what can be said of an expression.
            //
            // Whether the target is a place is asked of what it denotes and not of how it is spelled.
            // A name given a computed value is no more a place than the call it was given, and asked
            // by the spelling it came out one: `gross` was read through to the arithmetic behind it
            // and `gross.value` was an atom of its own, so a guard over the one settled nothing about
            // a construction over the other (#676).
            case Core.FieldAccess fa when !isAPlace(fa.target(), at)
                    && !Location.isStep(fa.target().type(), fa.field(), symbols) ->
                    affine(fa.target(), at, leaf);
            // A binding an expansion introduced (`let $0_n = n.value in $0_n * 2`) is what an
            // arithmetic helper becomes, so reading through it is reading the arithmetic the author
            // wrote.
            case Core.LetIn li -> {
                LinearForm<FactSubject> bound = affine(li.value(), at, leaf);
                yield bound == null ? null : affine(li.body(), at,
                        n -> n instanceof Core.Read r && r.binding().equals(li.binder().id())
                                ? bound : leaf.apply(n));
            }
            default -> null;
        };
    }

    /** What {@code e} folds to where every part of it is written out, or {@code null} where any part
     * of it is computed at run time and there is nothing to fold. */
    static Object folded(Core e) {
        Hir.Expr written = asWrittenValue(e);
        return written == null ? null : ConstEval.eval(written).orElse(null);
    }

    /** The number {@code e} folds to at compile time, or {@code null} where it folds to none. */
    static BigDecimal constantNumber(Core e) {
        Object folded = folded(e);
        if (folded instanceof Long n) {
            return BigDecimal.valueOf(n);
        }
        return folded instanceof BigDecimal d ? d : null;
    }

    /** A linear form scaled by a constant, when one side is a bare constant (a scalar multiply); null
     * when neither side is constant (a non-linear product). */
    static <A> LinearForm<A> scale(LinearForm<A> a, LinearForm<A> b) {
        if (a == null || b == null) {
            return null;
        }
        if (a.coefs().isEmpty()) {
            return b.times(a.constant());
        }
        return b.coefs().isEmpty() ? a.times(b.constant()) : null;
    }

    /** The affine form of an expression: a numeric atom, a newtype construct's wrapped value, or
     * {@code null}. */
    LinearForm<FactSubject> affineOf(Core e, Denotations at) {
        return affine(e, at, n -> {
            // A newtype built around a number is that number here. What makes it one is the
            // declaration, which `affineScalarBase` asks; a construction of it has the one field the
            // declaration gives it.
            if (n instanceof Core.Construct nd
                    && affineScalarBase(Type.ref(nd.typeName())) != null) {
                return affineOf(nd.values().get(0).value(), at);
            }
            Core written = writtenValue(n, at);
            if (written != null && written != n) {
                return affineOf(written, at);
            }
            // An operation answering a number it was given is that number here, whatever type it
            // answers it in: `Decimal.fromInt(n)` is `n`, so a guard about `n` is about the call as
            // well. Read through rather than made an atom of its own, which would leave the two
            // unrelated and the guard saying nothing about the construction.
            Core answered = DischargeRules.answersItsArgument(n);
            if (answered != null) {
                return affineOf(answered, at);
            }
            // A list written out has as many elements as it is written with, whatever they are.
            BigDecimal counted = writtenSize(n, at);
            if (counted != null) {
                return LinearForm.constant(counted);
            }
            // A name given arithmetic over terms the check names is related to that arithmetic (spec
            // §invariant-discharge-terms). Read through it, as the `let` node above is read through:
            // the name and the expression it was given are one value, and reading one as an atom of
            // its own leaves a guard on the name saying nothing about the value it was built from.
            LinearForm<FactSubject> given = givenForm(n, at);
            if (given != null) {
                return given;
            }
            FactSubject atom = atomOf(n, at);
            return atom == null ? null : LinearForm.atom(atom);
        });
    }

    /**
     * The form of what a name was given, where the name stands for a term of its own and what it was
     * given is arithmetic this can read. A name given a location is not this — {@link #atomOf}
     * answers that with the location, which is what the seeding wrote about.
     */
    private LinearForm<FactSubject> givenForm(Core e, Denotations at) {
        if (!(e instanceof Core.Read r) || !computesAsWhatItWasGiven(r.binding(), at)
                || affineScalarBase(e.type()) == null) {
            return null;
        }
        Core given = at.valueOf(r.binding());
        return given == null || given == e ? null : affineOf(given, at);
    }

    /**
     * How many elements a size call over a list written out counts, or {@code null} where its
     * argument is not one.
     *
     * <p>What the elements are is not asked. Whether a value is <em>written</em>
     * ({@link #isWritten}) is a question about the whole of it, down to every part, and it is the
     * right question where a construction is read as the value it builds — there a computed part is
     * a value the source does not hold. Counting reads the line the list is written on, and three
     * elements written there are three however each was arrived at. Asking the stronger question
     * left a list of parameters with a length nothing knew, and an invariant over it with no guard
     * an author could write: the length is not a value any condition could settle.
     */
    BigDecimal writtenSize(Core e, Denotations at) {
        Core container = DischargeRules.sizeArgOf(e);
        if (container == null) {
            return null;
        }
        return listedOut(container, at) instanceof Core.ListLit list
                ? BigDecimal.valueOf(list.elements().size()) : null;
    }

    /** The list {@code e} is, written where it is or written where the name it is was given one. */
    private Core listedOut(Core e, Denotations at) {
        if (!(e instanceof Core.Read r)) {
            return e;
        }
        Core given = at.valueOf(r.binding());
        return given == null || given == e ? e : listedOut(given, at);
    }

    static <A> LinearForm<A> negate(LinearForm<A> f) {
        return f == null ? null : f.negate();
    }

    static <A> LinearForm<A> add(LinearForm<A> a, LinearForm<A> b, boolean subtract) {
        if (a == null || b == null) {
            return null;
        }
        return subtract ? a.minus(b) : a.plus(b);
    }

    /**
     * The canonical atom key of a numeric value: a location ({@code x}, {@code p.a}, a newtype's
     * value), a size call over a nameable container, or anything else {@link #termKey} names — and
     * {@code null} where the value is not a number the domain carries, or where the term grammar
     * names it nothing. A call the representation did not keep standing is the second of those: what
     * a behavior answered is outside that grammar, so it is no more an atom than it was.
     *
     * <p>An atom exists because a value can be pointed at, not because anything is known of it. Two
     * writings of one value are one atom and so one unknown, which is the whole of what an atom
     * asserts; what is known of it is what a guard states and nothing else. Requiring something to
     * have been said before a value could be an atom made the first guard about a value the one that
     * could not be read, since it was read to decide whether that value had a name at all.
     */
    FactSubject atomOf(Core e, Denotations at) {
        FactSubject size = sizeAtomOf(e, arg -> bodyKey(arg, at));
        if (size != null) {
            return size;
        }
        // Read where it is going to be an answer, and not before: what a value is called is a walk
        // of the whole expression, and a value of a type the domain carries nothing of takes no atom
        // however it was written.
        return carriesANumber(e) ? atomOfIdentity(subjectOf(e, at), e, at) : null;
    }

    /**
     * What a position is called, and the atom it is where the numeric domain carries one.
     *
     * <p>Both from one reading. Where a value is a number the domain carries, its atom <em>is</em>
     * its subject — the same identity, recorded with how that type's values are spaced. Asked
     * separately the expression is read once for each, and a caller asking it of every level of a
     * field chain pays more than the chain is long (#826).
     *
     * <p>Not every position is both. A size takes an atom the symbolic reader builds over the
     * container it counts, which is not what the position is called; and a position of a type the
     * domain carries nothing of — an enumeration, a string — is called something and is no number.
     */
    Position positionOf(Core e, Denotations at) {
        FactSubject size = sizeAtomOf(e, arg -> bodyKey(arg, at));
        FactSubject key = subjectOf(e, at);
        if (size != null) {
            return new Position(key, size);
        }
        return new Position(key, carriesANumber(e) ? atomOfIdentity(key, e, at) : null);
    }

    /** What a position is called, and the atom it is — either may be absent. */
    record Position(FactSubject key, FactSubject atom) {}

    /** Whether the numeric domain carries values of what {@code e} answers at all. A number the term
     * grammar cannot read is still a number, which is why an atom asks this of the type and not of
     * whether the expression has a symbolic key. */
    private boolean carriesANumber(Core e) {
        return affineScalarBase(e.type()) != null;
    }

    /** {@code identity} as the atom of the value at {@code e}: held to how that type's values are
     * spaced, and recorded against the arithmetic it was built by. */
    private FactSubject atomOfIdentity(FactSubject identity, Core e, Denotations at) {
        FactSubject atom = named(identity, granularityOf(e.type()));
        if (atom != null) {
            recording(atom, e, at);
        }
        return atom;
    }


    /**
     * Records how {@code atom} was computed, where it stands for arithmetic the affine fragment
     * cannot carry.
     *
     * <p>Here because this is where such an atom is named, and the name is what everything else
     * about it is filed under: a second place deciding which expressions are products would be a
     * second answer to keep in step with this one. It is the same reason the spacing of an atom is
     * recorded here ({@link #named}).
     *
     * <p>What is recorded is how the value was computed and not what it lies between. What it lies
     * between depends on what the path assumed, and the path is not something the naming of an
     * expression knows — which is why the walk that reads the operands is not handed one.
     */
    private void recording(FactSubject atom, Core e, Denotations at) {
        if (!(asOperator(e) instanceof Core.Binary b)) {
            return;
        }
        Derivation made = switch (b.op()) {
            case MUL -> product(b, at);
            case DIV -> quotient(b, at);
            default -> null;
        };
        if (made == null) {
            return;
        }
        Derivation had = derivations.putIfAbsent(atom, made);
        if (had != null && !sameDerivation(had, made)) {
            throw new OneTermTwoDerivations("atom `" + atom.rendered() + "` was computed as "
                    + had + " and as " + made);
        }
    }

    /** The product {@code b} is, or null where either factor is a value nothing can be said of. A
     * factor that is a written constant is not this: that product is a scalar multiply and the
     * fragment carries it ({@link #scale}). */
    private Derivation product(Core.Binary b, Denotations at) {
        LinearForm<FactSubject> left = affineOf(b.left(), at);
        LinearForm<FactSubject> right = affineOf(b.right(), at);
        return left == null || right == null ? null : new Derivation.Product(left, right);
    }

    /**
     * The quotient {@code b} is, or null where there is no rule about it.
     *
     * <p>Only over whole numbers, and only by a divisor that is a whole number other than zero.
     * {@code /} on {@code Int} truncates toward zero, which is a step nothing about the divisor
     * changes; on {@code Decimal} it rounds to a precision the run time sets (spec §stdlib-decimal),
     * and what that rounding does to an end is not something this reads. A divisor the path only
     * bounds away from zero is not read either — it is the sign and the magnitude of a written
     * number that the rule is about.
     *
     * <p>And only by a divisor an {@code Int} can hold. The arithmetic composed here is over
     * numbers of any size, so a written form can reach one no {@code Int} is; the rule is about the
     * operator, whose divisor is an {@code Int}. Asked for one as the other this threw, and a throw
     * here is read as a limit of the analysis and swallowed — which left the construction reported
     * as nothing at all rather than as a clause nothing here establishes.
     */
    private Derivation quotient(Core.Binary b, Denotations at) {
        if (granularityOf(b.type()) != Granularity.DISCRETE) {
            return null;
        }
        LinearForm<FactSubject> numerator = affineOf(b.left(), at);
        LinearForm<FactSubject> divisor = affineOf(b.right(), at);
        if (numerator == null || divisor == null || !divisor.coefs().isEmpty()) {
            return null;
        }
        BigDecimal written = divisor.constant();
        if (written.signum() == 0 || written.stripTrailingZeros().scale() > 0
                || !isWholeNumberAnIntHolds(written)) {
            return null;
        }
        return new Derivation.Quotient(numerator, written.longValue());
    }

    /** Whether {@code written} is a number an {@code Int} is (spec §primitives), which is what the
     * operator's divisor is. */
    private static boolean isWholeNumberAnIntHolds(BigDecimal written) {
        return written.compareTo(BigDecimal.valueOf(Long.MIN_VALUE)) >= 0
                && written.compareTo(BigDecimal.valueOf(Long.MAX_VALUE)) <= 0;
    }

    /**
     * Whether two readings computed a value the same way.
     *
     * <p>Asked of the numbers and not of how they are written: a coefficient of {@code 0.10} and one
     * of {@code 0.1} are one number, and a record's own equality says they are two. What this is for
     * is catching the check naming two values alike, and a difference in scale is not that.
     */
    private static boolean sameDerivation(Derivation a, Derivation b) {
        return switch (a) {
            case Derivation.Product one -> b instanceof Derivation.Product other
                    && sameForm(one.left(), other.left())
                    && sameForm(one.right(), other.right());
            case Derivation.Quotient one -> b instanceof Derivation.Quotient other
                    && one.divisor() == other.divisor()
                    && sameForm(one.numerator(), other.numerator());
        };
    }

    private static boolean sameForm(LinearForm<FactSubject> a, LinearForm<FactSubject> b) {
        if (a.constant().compareTo(b.constant()) != 0 || !a.coefs().keySet().equals(b.coefs().keySet())) {
            return false;
        }
        return a.coefs().entrySet().stream()
                .allMatch(one -> one.getValue().compareTo(b.coefs().get(one.getKey())) == 0);
    }

    /**
     * One atom this said was computed two ways.
     *
     * <p>Beside {@link OneTermTwoKinds} and for its reason. A term is a value, and a value is
     * computed by whatever computes it — so an atom recorded as two different pieces of arithmetic
     * is the naming and the reading disagreeing about which value the atom is, and every bound
     * derived under that name is about neither of them.
     */
    static final class OneTermTwoDerivations extends TheCheckDisagreesWithItself {

        OneTermTwoDerivations(String message) {
            super(message);
        }
    }

    /** The atom of the size {@code e} takes of a container {@code key} can name, or null where it
     * takes none or names none. */
    FactSubject sizeAtomOf(Core e, java.util.function.Function<Core, Term> key) {
        Core container = DischargeRules.sizeArgOf(e);
        if (container == null) {
            return null;
        }
        Term arg = key.apply(DischargeRules.sizeSource(container));
        return arg == null ? null : sizeKeyOf(((Core.PreservedCall) e).operation(), arg);
    }

    /** The size {@code size} takes of {@code container}, named as the whole number it is. A size
     * counts elements, so there is nothing to decide about how its values are spaced. It is the call
     * that takes it and nothing besides, which is the term a clause reading one builds and the term a
     * guard stating one builds — so the two are one value rather than two writings that have to keep
     * spelling each other alike. */
    FactSubject sizeKeyOf(ValueName size, Term container) {
        return named(interned.called(size, List.of(container)), Granularity.DISCRETE);
    }

    /**
     * The number {@code measure} answers of {@code from} and {@code to}, named as the call it is.
     *
     * <p>The same shape a clause writing that measure builds, so a rule stated in it and an invariant
     * written in it name one value. How its values are spaced is read off what the library declares
     * the measure to answer, which is what a clause reading the call is named with too — a count of
     * whole days is one thing wherever it is written.
     */
    FactSubject measureKeyOf(ValueName.Stdlib measure, Term from, Term to) {
        Prelude.PreludeEntry counts = Prelude.entry(measure.qualified());
        return named(interned.called(measure, List.of(from, to)),
                granularityOf(counts.signature().result()));
    }

    /**
     * The atom a rule counting {@code e} would have bounded, or null where there is no such atom.
     *
     * <p>Written because the identity is not the field's name. A size is keyed on the shape
     * {@code length(<what the container keys as>)}, and what the container keys as is a location —
     * {@code demo.Bag.fields.0} and not {@code xs} — so a caller spelling that shape itself would be
     * agreeing with this by hand at every place it asked. What a value of a type is counted by is
     * {@link NumericMeasures}' answer, and the container's key is {@link #bodyKey}'s, and this is the
     * two of them put together in the one order they go together in.
     *
     * <p>Recognised and not made. {@link #sizeKeyOf} names a shape whether or not anything has
     * spoken about it, which is what a clause reading one needs; a reader asking what was said about
     * a field wants the name a clause already gave it, and answering with a fresh one would put an
     * atom nothing bounds into the domain and call that an answer.
     */
    FactSubject takenAtomOf(Core e, Type type, Denotations at) {
        ValueName.Stdlib counts = NumericMeasures.takenOf(type, symbols);
        if (counts == null) {
            return null;
        }
        Term container = bodyKey(e, at);
        return container == null ? null : FactSubject.of(interned.calledIfBuilt(counts, List.of(container)));
    }

    /**
     * One term this gave two kinds of number.
     *
     * <p>Apart from everything else the check can fall over on, and for a reason. Those are shapes it
     * has no rule for, and answering them with silence is what fail-open means. This is the check
     * disagreeing with itself about one of its own terms: a term is a value, and a value is one kind
     * of number, so every relation recorded against a term that is two of them relates the wrong
     * things. Swallowed, it produces a body with no findings, which is what a body with nothing to
     * report produces.
     *
     * <p>What it is about has narrowed. A term was a string written out of its parts, and two values
     * could write one — a collision this would catch only where the two happened to be numbers spaced
     * differently. Terms are held by what they are made of now, so that route is gone and what is
     * left is the check handing one value two spacings.
     */
    static final class OneTermTwoKinds extends TheCheckDisagreesWithItself {

        OneTermTwoKinds(String message) {
            super(message);
        }
    }

    /** {@code key}, with how its values are spaced recorded against it. A key is what a value is
     * called and a kind is what the value is, so one key is one kind: two would mean this named two
     * values alike, and everything recorded under the name would be about neither of them. */
    private FactSubject named(Term key, Granularity g) {
        return key == null ? null : named(FactSubject.of(key), g);
    }

    /** The same, of a subject already made. Both spellings record here, so an atom reached by either
     * is held to the one kind. */
    private FactSubject named(FactSubject subject, Granularity g) {
        if (subject == null) {
            return null;
        }
        Granularity had = atomKinds.putIfAbsent(subject, g);
        if (had != null && had != g) {
            throw new OneTermTwoKinds("atom `" + subject.rendered() + "` is " + had
                    + " and " + g);
        }
        return subject;
    }

    /** How the values of a numeric type are spaced. */
    Granularity granularityOf(Type t) {
        Type carrier = affineScalarBase(t);
        if (carrier == Type.INT) {
            return Granularity.DISCRETE;
        }
        if (carrier == Type.DECIMAL) {
            return Granularity.DENSE;
        }
        throw new IllegalStateException("not a number the domain carries: " + Type.show(t));
    }

    /** The spacing of every atom {@code f} is written over, for the domain to record. Every one of
     * them was named here, so one that is not is a form built somewhere this cannot answer for. */
    Map<FactSubject, Granularity> kindsOf(LinearForm<FactSubject> f) {
        return kindsOfAtoms(f.coefs().keySet());
    }

    /** The same, for a name being given a form: the name is an atom too, and its own type says how
     * its values are spaced. */
    Map<FactSubject, Granularity> kindsOf(LinearForm<FactSubject> f, FactSubject atom, Type type) {
        Map<FactSubject, Granularity> out = new HashMap<>(kindsOf(f));
        Granularity g = granularityOf(type);
        named(atom, g);
        out.put(atom, g);
        return out;
    }

    private Map<FactSubject, Granularity> kindsOfAtoms(Set<FactSubject> atoms) {
        Map<FactSubject, Granularity> out = new HashMap<>();
        for (FactSubject atom : atoms) {
            Granularity g = atomKinds.get(atom);
            if (g == null) {
                throw new IllegalStateException("atom `" + atom.rendered() + "` was not named here");
            }
            out.put(atom, g);
        }
        return out;
    }

    /** An expression's canonical key: a location names itself, and everything else is read
     * structurally. */
    Term bodyKey(Core e, Denotations at) {
        return termKey(e, at, Map.of(), 0, Leaf.SYMBOLIC);
    }

    /** The identity a fact about {@code e} is filed under: the same algebra, taking an atom of its
     * own where the grammar runs out rather than answering nothing. */
    private Term identityOf(Core e, Denotations at) {
        return termKey(e, at, Map.of(), 0, Leaf.AN_EVALUATION);
    }

    /**
     * The subject a fact about {@code e} is about: the atom where the numeric domain carries one, and
     * the canonical key of the expression otherwise.
     *
     * <p>One place answers it. Three readers worked the same fallback out for themselves, and a
     * reader that decides for itself which of the two a value is named by is a reader that can decide
     * it differently from the one beside it.
     */
    FactSubject subjectOf(Core e, Denotations at) {
        return FactSubject.of(identityOf(e, at));
    }

    /**
     * The subject the place {@code binding} is: what a fact about a binding nothing else names is
     * about.
     *
     * <p>Here because identity is built here and nowhere else. {@link Denotations} records what each
     * binding's subject is and is handed it; asked to work it out from what the binding denotes, it
     * would be a second authority on which value something is, and the two would answer differently
     * the moment a binding names a value that is not a place.
     */
    FactSubject placeSubject(BindingId binding) {
        return FactSubject.of(placeTerm(binding));
    }

    /** What the term grammar names the place {@code binding} is by: the place it is. Said here for
     * the same reason every other term is. */
    Term placeTerm(BindingId binding) {
        return interned.at(Location.of(binding));
    }

    /**
     * The subject of what the present optional {@code optional} holds.
     *
     * <p>An optional and what stands under it are two values, so opening one is the only place a
     * {@code match} arm names something other than the value it was given. Which value that is
     * follows from the optional's own — two arms opening one optional open one value — and it is
     * asked here for the same reason every other identity is.
     */
    FactSubject heldBy(FactSubject optional) {
        return optional == null ? null : FactSubject.of(interned.held(optional.identity()));
    }

    /**
     * The subject one evaluation of {@code e} is — the same one every time this occurrence is asked
     * about, and one no other occurrence can be given.
     *
     * <p>Kept in a table rather than made afresh, because a subject made twice is two subjects and a
     * fact filed under the first is then about neither. The table is keyed by the node, which is what
     * an occurrence is here: two writings of one call are two nodes and so two evaluations, which is
     * the answer for a value nothing may share and the safe answer for one that may.
     */
    private EvaluationId evaluationIdOf(Core e) {
        if (e == null) {
            return null;
        }
        return evaluations.computeIfAbsent(asWritten(e),
                node -> new EvaluationId(shapeOf(node), node.pos()));
    }

    /**
     * Records that {@code made} is {@code from} built again — the same evaluation, reached through a
     * tree this check rewrote rather than through the one the author wrote.
     *
     * <p>Held here because which occurrence a node is, is an identity question, and identity has one
     * authority. A reading that replaces a conditional rebuilds every node on the way to it
     * ({@code Core.mapAll} makes a new parent whenever a child changed), so the very same call
     * arrives as a different object in each reading. Left unrecorded, each reading would give it an
     * evaluation of its own, and a fact taken in one would be about nothing in the next.
     *
     * <p>A rebuild is not a second evaluation. Something that really does evaluate twice — two calls
     * written out, one call inside a fold — is two nodes and never comes through here, so the two
     * stay apart.
     */
    void rebuilt(Core made, Core from) {
        if (made != from) {
            builtFrom.put(made, from);
        }
    }

    /** The node {@code e} was built from, however many rewrites ago — and {@code e} itself where it
     * is the one that was written. */
    Core asWritten(Core e) {
        Core from = e;
        Core next;
        while ((next = builtFrom.get(from)) != null) {
            from = next;
        }
        return from;
    }

    /** What to call an evaluation in a message: the kind of expression it is. */
    private static String shapeOf(Core e) {
        return switch (e) {
            case Core.Call _ -> "an answer";
            case Core.Apply _ -> "what a function value answered";
            default -> "a value";
        };
    }

    /**
     * How a value a construction is being given is named where a clause reads it: a location names
     * itself, and a container built from one by an operation the table covers names that
     * construction. Anything else names nothing.
     *
     * <p>What is named. A location is: the seeding writes about locations, so a clause reading one
     * reads something. A container built by an operation the table covers is, since the table is a
     * rule about it. A number the term grammar names is, whatever computes it — the domain carries
     * it, and a clause reading it reads an unknown the guards may or may not have settled. A number
     * that grammar names nothing, such as what a behavior answered, is not. A value of any other kind
     * is named
     * only where a guard on this path spoke about it, since a clause reading it has otherwise nothing
     * to be read against.
     *
     * <p>What is not named is not thereby discharged. Its construction is silent, and the silence is
     * this check's flagging policy rather than a proof: the run-time check stands for the whole of
     * such an invariant. Widening it is a matter of naming more values here.
     */
    FactSubject reportableSite(Core e, Denotations at, Known k) {
        // A value written out is not a site at all. There is nothing to state of `"xyz"` that the
        // text does not already say, so there is no guard an author could add — and this is a rule
        // about what is worth reporting, not about what is known. Asked of the text rather than of
        // which arm a denotation is, since what was written is a fact about the value however it is
        // reached. Kept out of the judgment below rather than answered as "not readable": a written
        // value's key is one a guard naming a literal puts in `spoken` (`x == "xyz"` speaks of both
        // sides), so folded into the judgment it would come back readable through the second half.
        if (writtenValue(e, at) != null) {
            return null;
        }
        FactSubject subject = subjectOf(e, at);
        if (subject == null) {
            return null;
        }
        return intrinsicallyReadable(e, at) || k.speaksOf(subject) ? subject : null;
    }

    /**
     * Whether the check's own semantics make {@code e} something a clause can be read against, before
     * anything a path has said.
     *
     * <p>A place is: the seeding writes about places, whatever their type states. A computed value is
     * where the numeric domain built a form for it or a rule says how it was made. Anything else is
     * not, and stays not until a guard on the path speaks of it — which is the other half of the
     * question and is asked of {@link Known}, not here.
     *
     * <p>Asked of the expression, so a name for it answers the same. That is what makes naming an
     * expression not change what is known of it.
     */
    boolean intrinsicallyReadable(Core e, Denotations at) {
        return isAPlace(e, at)
                || (bodyKey(e, at) != null && (affineOf(e, at) != null || namedByRule(e, at)));
    }

    /**
     * The canonical key of an expression as a term, or {@code null} when nothing here can be named.
     * Two expressions with one key compute one value, which is the whole of what the fact set knows:
     * a guard and an invariant clause state the same predicate exactly when their calls key alike.
     *
     * <p>A location keys as the location it is, so which value a term is about is the binding it is
     * rooted at. A closure parameter is keyed by where it is bound rather than by its binding, so
     * {@code r -> r.a} and {@code row -> row.a} are one term while a free name inside the closure is
     * still the value it is and so is part of the term. Anything outside this grammar keys as
     * {@code null}, and the clause reading it is left opaque.
     */
    private Term termKey(Core raw, Denotations at, Map<BindingId, Term> bound, int depth,
                         Leaf leaf) {
        return naming(raw, at, bound, depth, leaf).term();
    }

    /**
     * What {@code raw} is called, or why it is called nothing.
     *
     * <p>Exhaustive over {@link Core} and carrying no default: a shape added to the language is a
     * compile error here rather than a value the check silently has nothing to say about. Which is
     * what the shapes below were — a call this reading kept standing fell through to nothing, so a
     * construction over one was left to the run-time check while the same construction over the same
     * helper expanded into the body was reported (#722).
     *
     * <p>A value is named by what computes it, where what computes it is a function of named parts.
     * So the parts decide most of this, and what decides the rest is what is being called: a module's
     * own helper is pure, the language's own operations are, and what an injected behavior answers is
     * not. That a call is still standing here is not one of the questions — whether a helper was
     * expanded into this body is a fact about the reading, not about the value it answers.
     */
    /**
     * What a walk over an expression does where the term grammar runs out.
     *
     * <p>Two readings, one walk. The symbolic domain wants to know whether it can read a value's
     * structure, and an answer of "no" is what leaves a clause over it opaque. Asking what a fact
     * about that value would be filed under is a different question with a different right answer:
     * the value is still one value, and it takes an atom equal to itself and to nothing else. Written
     * as two walks they would be two structural rules to keep agreeing, which is what a second
     * identity algebra would have been.
     */
    enum Leaf {
        /** Runs out: the shape has no term, and neither has anything built from it. */
        SYMBOLIC,
        /** Takes an atom of its own, so that what is built over it composes. */
        AN_EVALUATION
    }

    /** {@code c}'s arguments, with a size call's container peeled back to the one whose size it is.
     * Only where an identity is being built: what the symbolic reader keys a size as is its own
     * question, and answering it here would move a key nothing asked to be moved. */
    private List<Core> sizedOver(Core.PreservedCall c, Leaf leaf) {
        Core container = leaf == Leaf.AN_EVALUATION ? DischargeRules.sizeArgOf(c) : null;
        return container == null ? c.args() : List.of(DischargeRules.sizeSource(container));
    }

    /** The naming to answer with where the grammar runs out, which is nothing or the evaluation
     * itself. */
    private Naming ranOut(Core raw, Leaf leaf, Naming absent) {
        return leaf == Leaf.AN_EVALUATION
                ? new Naming.Named(interned.evaluated(evaluationIdOf(raw))) : absent;
    }

    private Naming naming(Core raw, Denotations at, Map<BindingId, Term> bound, int depth,
                          Leaf leaf) {
        Core e = asOperator(raw);
        BindingId root = rootBinding(e);
        if (root != null) {
            Term here = bound.get(root);
            return here != null ? new Naming.Named(interned.on(here, chainOf(e)))
                    : Naming.of(pathKey(e, at, leaf), Naming.Reason.A_BINDING_STANDS_FOR_NOTHING);
        }
        return switch (e) {
            case Core.Read _, Core.FieldAccess _ ->
                    Naming.of(pathKey(e, at, leaf), Naming.Reason.A_BINDING_STANDS_FOR_NOTHING);
            case Core.Int i -> new Naming.Named(interned.written(i.value()));
            case Core.Decimal d -> new Naming.Named(interned.written(d.value()));
            case Core.Str str -> new Naming.Named(interned.written(str.value()));
            case Core.Bool b -> new Naming.Named(interned.written(b.value()));
            // Named as the construction it is written as, which is the term two writings of one
            // date already shared when this arrived here as a call. The text alone would be the term
            // the string of it has, and a `Date` is not the text of one.
            case Core.Temporal t -> new Naming.Named(interned.called(
                    ValueName.Stdlib.namespace(t.kind().shown()),
                    List.of(interned.written(t.text()))));
            case Core.UnitValue u -> new Naming.Named(interned.unit(u.data()));
            case Core.Neg n -> over(List.of(n.operand()), at, bound, depth, leaf,
                    ps -> interned.negated(ps.get(0)));
            case Core.Binary b -> over(List.of(b.left(), b.right()), at, bound, depth, leaf,
                    ps -> interned.operator(b.op(), ps.get(0), ps.get(1)));
            case Core.ListLit l -> over(l.elements(), at, bound, depth, leaf, interned::list);
            case Core.Tuple t -> over(t.elements(), at, bound, depth, leaf, interned::tuple);
            case Core.TupleGet g -> over(List.of(g.tuple()), at, bound, depth, leaf,
                    ps -> interned.part(ps.get(0), g.index()));
            case Core.If iff -> over(List.of(iff.cond(), iff.then(), iff.els()), at, bound, depth, leaf,
                    ps -> interned.choice(ps.get(0), ps.get(1), ps.get(2)));
            case Core.OptionSome s -> over(List.of(s.value()), at, bound, depth, leaf,
                    ps -> interned.some(ps.get(0)));
            case Core.OptionNone none -> new Naming.Named(interned.none(none.type()));
            case Core.Block b -> {
                Map<BindingId, Term> inner = binding(bound, b.params(), depth);
                yield named(naming(b.body(), at, inner, depth + 1, leaf),
                        body -> interned.closure(b.params().size(), body));
            }
            case Core.LetIn li -> {
                Naming value = naming(li.value(), at, bound, depth, leaf);
                if (value instanceof Naming.Unnamed absent) {
                    yield absent;
                }
                Map<BindingId, Term> inner = binding(bound, List.of(li.binder()), depth);
                yield named(naming(li.body(), at, inner, depth + 1, leaf),
                        body -> interned.let(value.term(), body));
            }
            // A construction is a pure function of its fields, and a closure that builds one is what a
            // mapping usually is. The fields are held in declaration order, so two sites writing them
            // in different orders — or one of them through a spread — write one term.
            case Core.Construct nd -> over(nd.values().stream().map(Core.FieldValue::value).toList(),
                    at, bound, depth, leaf,
                    ps -> interned.built(nd.typeName(),
                            nd.values().stream().map(Core.FieldValue::field).toList(), ps));
            case Core.Match m -> {
                List<Core> arms = new ArrayList<>();
                arms.add(m.scrutinee());
                Map<BindingId, Term> outer = bound;
                List<Naming> answers = new ArrayList<>();
                for (Core.Case arm : m.cases()) {
                    Map<BindingId, Term> inner = arm.binding() == null ? outer
                            : binding(outer, List.of(arm.binding()), depth);
                    answers.add(naming(arm.body(), at, inner, depth + 1, leaf));
                }
                Naming scrutinee = naming(m.scrutinee(), at, bound, depth, leaf);
                yield joined(scrutinee, answers,
                        parts -> interned.matched(parts.get(0),
                                m.cases().stream().map(Core.Case::caseTypes).toList(),
                                parts.subList(1, parts.size())));
            }
            case Core.IfConstructed ic -> {
                Naming built = naming(ic.construct(), at, bound, depth, leaf);
                Map<BindingId, Term> inner = binding(bound, List.of(ic.binder()), depth);
                List<Naming> answers = new ArrayList<>();
                answers.add(naming(ic.then(), at, inner, depth + 1, leaf));
                for (Core.ElseArm arm : ic.els()) {
                    answers.add(naming(arm.body(), at, bound, depth, leaf));
                }
                yield joined(built, answers,
                        parts -> interned.attempted(parts.get(0),
                                ic.els().stream().map(arm -> arm.clause().orElse("")).toList(),
                                parts.subList(1, parts.size())));
            }
            // What the language's own operations answer, and what a module's own helper answers, are
            // functions of what they were given: the first because the language defines them, the
            // second because a helper is pure (spec §fn-rules). What an injected behavior answers is
            // neither, and a call to one is named by nothing.
            // A size is keyed over the container it is really the size of. An operation that answers
            // exactly as many as it was given does not change the number, which the discharge table
            // states as a relation between the two values (`Cardinality.SAME`) rather than as
            // something this check happens to follow — so it is an equality identity may read.
            case Core.PreservedCall c -> over(sizedOver(c, leaf), at, bound, depth, leaf,
                    ps -> interned.called(c.operation(), ps));
            case Core.Call c -> switch (c.fn()) {
                case Core.Reached reached -> switch (answersOf(reached.denotes())) {
                    case Naming.OfAName.AnswersNothing none ->
                            ranOut(raw, leaf, new Naming.Opaque(none.reason()));
                    case Naming.OfAName.Answers ignored -> over(c.args(), at, bound, depth, leaf,
                            ps -> interned.called(reached.denotes(), ps));
                };
                // A walk this compiler minted for a shape the backend lowers as a whole. The reading
                // this check is given keeps no such call, so one arriving is a pass having run over a
                // tree it was not written for rather than a value nothing can be said of.
                case Core.Emitted emitted -> ranOut(raw, leaf, unsupported(emitted.rendered()));
            };
            case Core.Apply _ -> ranOut(raw, leaf,
                    new Naming.Opaque(Naming.Reason.A_FUNCTION_VALUE_WAS_APPLIED));
            case Core.Unreachable _ -> new Naming.Opaque(Naming.Reason.NOTHING_IS_ANSWERED);
        };
    }

    /**
     * Whether {@code callee} answers a value two writings of a call to it share.
     *
     * <p>Asked of what the name was resolved to and of nothing else. A module's own helper is pure
     * and total, a value definition's body obeys a helper's rules, and the language's own operations
     * are what the language says they are — so a call to any of them answers one value wherever it is
     * written with the same arguments. Whether the reading this check is given expanded that helper
     * into the body is a fact about the reading and not about the value, which is why it is not asked
     * here: a helper that recurses is left standing and a helper that does not is expanded, and the
     * two answer the same question about the same call.
     *
     * <p>What a behavior answered is named by nothing (spec §invariant-discharge-terms). An injected
     * one could not be: its implementation is outside the language and may read the outside world, so
     * two asks are two answers. What is applied through a binding is the same — the binding may hold
     * an injected behavior, and what it holds is not a question about the name.
     */
    private Naming.OfAName answersOf(ValueName callee) {
        return switch (callee) {
            case ValueName.Behavior _ ->
                    new Naming.OfAName.AnswersNothing(Naming.Reason.A_BEHAVIOR_ANSWERED);
            case ValueName.Local _ ->
                    new Naming.OfAName.AnswersNothing(Naming.Reason.A_FUNCTION_VALUE_WAS_APPLIED);
            case ValueName.Helper _, ValueName.Stdlib _, ValueName.Builtin _, ValueName.OfType _ ->
                    new Naming.OfAName.Answers();
        };
    }

    /** A shape this has no term for, recorded where a test can read that it happened. */
    private Naming unsupported(String form) {
        List<String> watching = reading == Of.THE_DISCHARGE_TREE ? UNSUPPORTED : null;
        if (watching != null) {
            watching.add(form);
        }
        return new Naming.Unsupported(form);
    }

    /** {@code made} of what {@code first} and {@code rest} name, or the first of them that names
     * nothing. */
    private Naming joined(Naming first, List<Naming> rest,
                          java.util.function.Function<List<Term>, Term> made) {
        List<Term> terms = new ArrayList<>();
        if (first instanceof Naming.Unnamed absent) {
            return absent;
        }
        terms.add(first.term());
        for (Naming one : rest) {
            if (one instanceof Naming.Unnamed absent) {
                return absent;
            }
            terms.add(one.term());
        }
        return new Naming.Named(made.apply(terms));
    }

    /** {@code made} of what {@code naming} names, or why it names nothing. */
    private Naming named(Naming naming, java.util.function.UnaryOperator<Term> made) {
        return naming instanceof Naming.Unnamed absent ? absent
                : new Naming.Named(made.apply(naming.term()));
    }

    /** {@code made} of the terms {@code parts} are, or null where any of them is named by nothing. */
    private Naming over(List<Core> parts, Denotations at, Map<BindingId, Term> bound, int depth,
                        Leaf leaf, java.util.function.Function<List<Term>, Term> made) {
        List<Term> terms = new ArrayList<>();
        for (Core part : parts) {
            Naming one = naming(part, at, bound, depth, leaf);
            if (one instanceof Naming.Unnamed absent) {
                return absent;
            }
            terms.add(one.term());
        }
        return new Naming.Named(made.apply(terms));
    }

    /** {@code bound} with each of {@code binders} keyed by where it is bound rather than by which
     * binding it is, so two expressions that differ only in what they bound are one term. */
    Map<BindingId, Term> binding(Map<BindingId, Term> bound, List<Hir.Binder> binders, int depth) {
        Map<BindingId, Term> inner = new HashMap<>(bound);
        for (int i = 0; i < binders.size(); i++) {
            inner.put(binders.get(i).id(), interned.bound(depth, i));
        }
        return inner;
    }

    /** The binding at the head of a {@code x}/{@code x.a.b} chain, or {@code null} if {@code e} is not
     * one. */
    static BindingId rootBinding(Core e) {
        return switch (e) {
            case Core.Read r -> r.binding();
            case Core.FieldAccess fa -> rootBinding(fa.target());
            default -> null;
        };
    }

    /** The fields read along a {@code x.a.b} chain, from the head down. */
    static List<String> chainOf(Core e) {
        List<String> out = new ArrayList<>();
        chainInto(e, out);
        return out;
    }

    private static void chainInto(Core e, List<String> out) {
        if (e instanceof Core.FieldAccess fa) {
            chainInto(fa.target(), out);
            out.add(fa.field());
        }
    }

    /**
     * The key of a chain rooted at a binding: what the binding at its head is about, with the fields
     * read from it.
     *
     * <p>Which value the head is, is the walk's answer and not this one's. A binding is entered with
     * the subject facts about it are filed under ({@link Denotations.Means}), and reading it back is
     * all that happens here — where working it out again from what the binding denotes was a second
     * authority on identity, and one that cannot answer for a binding that names a value the grammar
     * has no term for. That is what a {@code match} arm needs: the value it opens is the one the
     * scrutinee already is, and a reading that derives identity from how the binding was introduced
     * has no way to say so.
     *
     * <p>Asked of the identity reading only. What the term grammar can name without taking an atom
     * is a different question with a different answer — a call to a behavior is named by nothing —
     * and {@link Leaf#SYMBOLIC} is where it is asked, so that reading still works from what the
     * binding denotes.
     *
     * <p>A newtype's {@code .value} is the same value as the newtype, which is {@link Location}'s
     * rule and is read here of any subject, so a value keyed one way through a binding and the other
     * way through a field is one value.
     */
    Term pathKey(Core e, Denotations at, Leaf leaf) {
        if (leaf == Leaf.AN_EVALUATION) {
            return subjectKey(e, at);
        }
        Location located = locationOf(e, at);
        return located != null ? interned.at(located) : keyOfNowhere(e, at);
    }

    /**
     * The subject of a chain: what its head was entered as, with the fields read off it.
     *
     * <p>A head nothing entered is a value this reading knows nothing about, and it takes an atom of
     * its own — the same answer a shape outside the grammar gets, for the same reason.
     *
     * <p>Always answers. Every value has an identity, whether or not anything can be said about it,
     * so there is no reading here that comes back with nothing and no step that has to allow for one.
     * The reading beside this one does — what the term grammar can name runs out, and says so with
     * {@code null} — and the two are not the same question.
     */
    private Term subjectKey(Core e, Denotations at) {
        return switch (e) {
            case Core.Read r -> {
                FactSubject subject = at.subject(r.binding());
                yield subject != null ? subject.identity()
                        : interned.evaluated(evaluationIdOf(e));
            }
            case Core.FieldAccess fa ->
                    Location.isStep(fa.target().type(), fa.field(), symbols)
                            ? interned.on(subjectKey(fa.target(), at), List.of(fa.field()))
                            : subjectKey(fa.target(), at);
            default -> interned.evaluated(evaluationIdOf(e));
        };
    }

    /**
     * The same, for a chain already found to be nowhere — so what it is read from is nowhere too.
     *
     * <p>A chain names a location exactly when the binding at its head does ({@link Location#of}
     * answers {@code x.a.b} by answering {@code x} and then reading the fields off it, and reading a
     * field off somewhere never reaches nowhere). So a chain that is nowhere is one whose every step
     * is nowhere, and the question is answered once for the whole of it rather than again at each
     * step — asked at each step it walks what is left of the chain each time, and a chain costs more
     * than the chain is long (#826).
     */
    private Term keyOfNowhere(Core e, Denotations at) {
        return switch (e) {
            // What the walk recorded the term grammar names it by, and null where it names it by
            // nothing. A chain is asked of this only once it has been found not to be a place.
            case Core.Read r -> at.termOf(r.binding());
            case Core.FieldAccess fa -> {
                if (!Location.isStep(fa.target().type(), fa.field(), symbols)) {
                    yield keyOfNowhere(fa.target(), at);
                }
                Term base = keyOfNowhere(fa.target(), at);
                yield base == null ? null : interned.on(base, List.of(fa.field()));
            }
            default -> null;
        };
    }

    /**
     * Whether {@code binding}'s name may be read as the workings of the expression it was given: what
     * that expression is arithmetic over, what rule names it, read of the name as well.
     *
     * <p>Asked here rather than left as which arm a denotation is. Two readers tested one arm of
     * one classification for it, and an arm of a sum is a poor way to ask: the arm they tested said
     * what a binding is not — not a place, not text, not nameless — so what those readers meant held
     * by falling through the others, and removing an arm silently widened what they read. Named, the
     * question is one thing to answer and one thing to get wrong.
     *
     * <p>Not the same as following what a name was given. {@link #writtenValue} does that too, and
     * does it whatever the name denotes, because what was written is a fact about the value however
     * it is reached. This is about carrying a computation across a name, which a name given text or
     * given a place does not do: the text folds and the place is the atom, and neither is arithmetic
     * to read through to.
     *
     * <p>Worked out from what is asked elsewhere: where the binding is, what names it, and what it
     * was written as. Each of those is a question of its own with an answer of its own, and this one
     * is the three of them together — where a classification holding all three at once made the
     * answer to one of them depend on which other answers were left.
     */
    boolean computesAsWhatItWasGiven(BindingId binding, Denotations at) {
        Core given = at.valueOf(binding);
        return at.locationOf(binding) == null && at.termOf(binding) != null
                && (given == null || writtenValue(given, at) == null);
    }

    /**
     * Whether {@code e} is a place: somewhere the seeding writes about, whatever value happens to be
     * there.
     *
     * <p>Asked as a question about what may be done with it, and not by taking the location and
     * reading nothing off it but whether there was one. The two came apart when an arm stopped making
     * a value of its own: what a {@code match} opens is a place, so a clause may be read against it
     * and the seeding writes about it, while which value it is, is the one the scrutinee already was.
     * A reader wanting the second asks {@link #subjectOf}, and a reader holding a {@link Location} to
     * decide the first is one step away from deciding the second from it too.
     */
    boolean isAPlace(Core e, Denotations at) {
        return locationOf(e, at) != null;
    }

    /** The location {@code e} is, or {@code null} where it is a computed value rather than a place.
     *
     * <p>For the two readings that want the location itself: what a binding denotes, and what the
     * term grammar names a chain by. A reader that only wants to know whether there is one asks
     * {@link #isAPlace}. */
    Location locationOf(Core e, Denotations at) {
        return Location.of(e, symbols, at::locationOf);
    }

    /**
     * What {@code e} is written as, where it is a written value or a name given one — and
     * {@code null} where it is computed from anything.
     *
     * <p>Found by following what a name was given, however many names deep, and asked of what the
     * following ends at. A name is what it was given whatever kind of thing that is, so this is one
     * rule and not one per kind of binding: a {@code match} arm opening a value written into the
     * source opens that written value, for the same reason a {@code let} given it does.
     *
     * <p>{@code seen} ends a chain that has no end. Nothing the walk records is one — a binding is
     * entered under what stood before it — but a reading that follows what it is handed says what it
     * does with a chain it was handed, rather than leaving it to whoever built it.
     */
    Core writtenValue(Core e, Denotations at) {
        return writtenValue(e, at, new HashSet<>());
    }

    /** Where a test counts the steps this takes following what a name was given, and null everywhere
     * else. What a chain of names costs is not something an answer says. */
    static long[] FOLLOWED;

    /**
     * What the end of the chain from {@code binding} was written as, and the value it was given when
     * that was worked out.
     *
     * <p>Kept because the answer is about the binding and not about the ask. A reading of arithmetic
     * follows a name, then follows what that name was given, and so on down, so a chain of names was
     * walked once per link and cost the square of its length. What is remembered is the following and
     * not the fact — a binding still stands for what it was given, and this says only that the
     * following of it has been done.
     *
     * <p>Held against the environment it was worked out in, and thrown away when that is not the one
     * being asked about. What a name was given is the walk's answer, and the walk answers differently
     * as it goes: a name whose chain reaches a binding the walk had not entered yet reaches nothing,
     * and the same name reaches text once it has. Remembered across the two, the earlier answer would
     * stand where the later one is owed — and it did, over three constructions, until the environment
     * became part of what is remembered.
     */
    private record Followed(Denotations at, Core given, Core written) {}

    private final Map<BindingId, Followed> followed = new HashMap<>();

    private Core writtenValue(Core e, Denotations at, Set<BindingId> seen) {
        long[] counting = FOLLOWED;
        if (counting != null) {
            counting[0]++;
        }
        if (e instanceof Core.Read r) {
            Core given = at.valueOf(r.binding());
            if (given == null || given == e) {
                return null;
            }
            Followed had = followed.get(r.binding());
            if (had != null && had.at() == at && had.given() == given) {
                return had.written();
            }
            if (!seen.add(r.binding())) {
                return null;
            }
            Core written = writtenValue(given, at, seen);
            followed.put(r.binding(), new Followed(at, given, written));
            return written;
        }
        return isWritten(e) ? e : null;
    }

    /**
     * Whether {@code e} is a value written out rather than computed from anything: a literal, and a
     * list or a construction whose every part is one. A table written into the source is this — every
     * row of it is there to read — and there is no guard an author could add about it, which is what
     * naming it at a construction site would ask for.
     */
    static boolean isWritten(Core e) {
        return isWritten(e, Set.of());
    }

    /** The same, where {@code written} names the bindings an expansion introduced for values that
     * were themselves written. A helper called on written arguments is a written value: what it
     * expands to binds each argument and reads it back, which is the source's own text moved. */
    static boolean isWritten(Core e, Set<BindingId> written) {
        return switch (e) {
            // A temporal is one of the literals the language has (spec
            // §a-temporal-value-is-written-as-a-literal), so it is written wherever it stands. It
            // was carried here as a call and answered `false` in this switch's default while
            // `asWrittenValue` was writing it back out — one value, two answers about whether the
            // source holds it.
            case Core.Int _, Core.Decimal _, Core.Str _, Core.Bool _, Core.Temporal _,
                 Core.UnitValue _ -> true;
            case Core.Neg n -> isWritten(n.operand(), written);
            case Core.Read r -> written.contains(r.binding());
            case Core.ListLit list -> list.elements().stream().allMatch(x -> isWritten(x, written));
            case Core.Tuple t -> t.elements().stream().allMatch(x -> isWritten(x, written));
            case Core.OptionSome s -> isWritten(s.value(), written);
            case Core.Construct nd ->
                    nd.values().stream().allMatch(v -> isWritten(v.value(), written));
            case Core.LetIn li -> {
                if (!isWritten(li.value(), written)) {
                    yield false;
                }
                Set<BindingId> inner = new HashSet<>(written);
                inner.add(li.binder().id());
                yield isWritten(li.body(), inner);
            }
            default -> false;
        };
    }

    /** Whether {@code e} is a container built by an operation the preservation table covers, over an
     * argument that is itself named. */
    boolean builtByRule(Core e, Denotations at) {
        if (!(e instanceof Core.PreservedCall call)) {
            return false;
        }
        DischargeRules.Source built = DischargeRules.builtFrom(call);
        return built != null && namedByRule(built.container(), at);
    }

    /**
     * Whether {@code e} names something without a guard having to have spoken about it: it is read all
     * the way down. A location is; so is a value composed of ones by a shape the term grammar reads —
     * a concatenation, a conditional, arithmetic, a container the preservation table covers. A call
     * the check has no rule about is not, and neither is anything built from one: nothing follows from
     * naming it, and its construction is left to the run-time check.
     */
    boolean namedByRule(Core e, Denotations at) {
        if (isAPlace(e, at)) {
            return true;
        }
        if (e instanceof Core.Read r) {
            // The name is the expression it was given, so the question is asked of that expression.
            // It was a flag recorded when the binding was entered, which is a second record of what
            // the initializer already answers.
            Core given = at.valueOf(r.binding());
            return computesAsWhatItWasGiven(r.binding(), at) && given != null && given != e
                    && (affineOf(given, at) != null || namedByRule(given, at));
        }
        Core read = asOperator(e);
        if (read instanceof Core.PreservedCall call
                && !DischargeRules.readsAsATerm(call.operation())) {
            return builtByRule(read, at);
        }
        // A call the representation did not keep standing answers something this check has no rule
        // about, whatever the operation behind it was.
        if (read instanceof Core.Call || read instanceof Core.Apply) {
            return false;
        }
        // Arithmetic is the numeric domain's to name. Where the domain builds a form, that form is
        // what a clause is read against; where it declines to — a variable product, an integer divide
        // — declining is a decision about what this check reasons over, and reporting a construction
        // it has decided not to reason over would be reporting the decision as the author's to fix.
        if (read instanceof Core.Binary bin && isArith(bin.op())) {
            return false;
        }
        // A conditional is one of its branches and which one is not decided here. Saying only that it
        // is that term reports every construction over one, including where both branches satisfy the
        // clause. Reading it is checking the construction on each branch under its own condition,
        // which this walk does not do, so it is not named until it does.
        if (read instanceof Core.If) {
            return false;
        }
        boolean[] all = {true};
        // A closure is not part of what names the value: the tables are rules about how many elements
        // there are and where they came from, and how each one is made has no bearing on either.
        Core.forEachChild(read, child -> all[0] = all[0]
                && (child instanceof Core.Block || namedByRule(child, at)));
        return all[0];
    }

    // --- what the two representations share ----------------------------------------------------

    /**
     * {@code e} as the value it is written as, for the one reader that is defined over written values:
     * the constant folder. A value written out is the same value in either representation, so this is
     * a rendering and not a second tree — everything computed answers with nothing, and the fold then
     * has nothing to fold.
     */
    static Hir.Expr asWrittenValue(Core e) {
        // Written over nothing, every one of them. A value rendered back out of what was computed is
        // the value and not the characters any of it came from: the fold has already been over them,
        // and what it arrived at may be a number no line of the file spells.
        return switch (e) {
            case Core.Int i -> new Hir.IntLit(i.value(), i.pos(), null);
            case Core.Decimal d -> new Hir.DecimalLit(d.value(), d.pos(), null);
            case Core.Str s -> new Hir.StringLit(s.value(), s.pos(), null);
            case Core.Bool b -> new Hir.BoolLit(b.value(), b.pos(), null);
            case Core.Neg n -> {
                Hir.Expr operand = asWrittenValue(n.operand());
                yield operand == null ? null : new Hir.Neg(operand, n.pos(), null);
            }
            case Core.Binary b -> {
                Hir.Expr left = asWrittenValue(b.left());
                Hir.Expr right = asWrittenValue(b.right());
                yield left == null || right == null ? null
                        : new Hir.Binary(b.op(), left, right, b.origin(), b.pos(), null);
            }
            case Core.PreservedCall call -> {
                List<Hir.Expr> args = written(call.args());
                yield args == null ? null
                        : new Hir.Apply(call.operation().name(), call.operation(),
                                reachOf(call.operation()), args, ConstructionOrigin.own(),
                                call.pos(), null);
            }
            // A temporal is written as a literal with its text spelled out (spec
            // §a-temporal-value-is-written-as-a-literal). Rendered here for the same reason every
            // other written form is: it is a value the author wrote, and a reader handed nothing for
            // it reads the rule around it as a rule about something unknown. Written back as the
            // construction it was written as, which is the form a report and `ConstEval` read.
            //
            // This used to be held to the calls answering a temporal — which took any behavior
            // answering a `Date` over written arguments for a date the source spells out, and let a
            // line be drawn where the compiler knows no value. What is written is the node now, and
            // nothing here decides it.
            case Core.Temporal t -> {
                ValueName.Stdlib namespace = ValueName.Stdlib.namespace(t.kind().shown());
                yield new Hir.Apply(namespace.qualified(), namespace, reachOf(namespace),
                        List.of(new Hir.StringLit(t.text(), t.pos(), null)),
                        ConstructionOrigin.own(), t.pos(), null);
            }
            // A case of an enumeration is written by naming it, so the value is the name.
            case Core.UnitValue unit -> Hir.Var.respelled(unit.data().name(),
                    new ValueName.OfType(unit.data().name(), unit.data(),
                            ConstructionOrigin.own()),
                    new ReachName.Bare(unit.data().name()), unit.pos(), null);
            case null, default -> null;
        };
    }

    /** Every argument as it was written, or null where any of them was computed. */
    private static List<Hir.Expr> written(List<Core> args) {
        List<Hir.Expr> out = new ArrayList<>();
        for (Core arg : args) {
            Hir.Expr each = asWrittenValue(arg);
            if (each == null) {
                return null;
            }
            out.add(each);
        }
        return out;
    }

    // --- helpers -------------------------------------------------------------------------------


    /** A read of {@code binder}, as the expression naming the value it holds. */
    static Core.Read read(Hir.Binder binder, Type type, SourcePos pos) {
        return new Core.Read(binder.name(), binder.id(), type, pos);
    }

    /** The block {@code e} is, following a name given one: a lambda handed to an operation the
     * representation keeps standing is never applied here, so it is bound to a name like any other
     * value and reaches the call as that name. */
    static Core.Block blockOf(Core e, Denotations at) {
        if (e instanceof Core.Block b) {
            return b;
        }
        return e instanceof Core.Read r && at.valueOf(r.binding()) instanceof Core.Block b ? b : null;
    }


    /** The type of {@code field} read from {@code owner}, or null where that is not a field of a
     * declaration this module can see. Asked of the one field, since resolving the whole
     * declaration's fields is a question about a declaration this reader may not own. */
    Type fieldType(Type owner, String field) {
        return owner instanceof Type.Ref r && symbols.declarations().declaration(r.name().key()) instanceof Hir.Data data
                ? TypeOps.fieldType(data, field, symbols) : null;
    }

    /** What a container hands its closure: a list's or set's element, a map's value (the key is the
     * other closure parameter and is not the one the table credits), an option's payload, and a
     * function's first parameter where what is held is the closure itself. */
    static Type elementType(Type t) {
        if (t instanceof Type.ListOf list) {
            return list.element();
        }
        if (t instanceof Type.SetOf set) {
            return set.element();
        }
        if (t instanceof Type.MapOf map) {
            return map.value();
        }
        if (t instanceof Type.OptionOf opt) {
            return opt.element();
        }
        if (t instanceof Type.FnOf fn && !fn.params().isEmpty()) {
            return fn.params().get(0);
        }
        return null;
    }

    /**
     * The number the affine domain can carry a value of {@code t} as, or null where it can carry
     * none.
     *
     * <p>This is the analyser's own capability and is named for the domain that has it. Two other
     * questions read like it and are not it: whether arithmetic is closed over the type, which the
     * language answers only for a newtype directly over a number ({@link
     * TypeOps#directNumericNewtypeBase}, spec §newtype-arithmetic), and whether the type is an
     * ordered number, which reaches the recursive base ({@link TypeOps#base}, ADR-0047). Answering
     * this one with the first is how a comparison the language accepts stopped reaching the
     * reasoning.
     *
     * <p>The carrier and not a yes: a caller that has to know whether it is stepping through whole
     * numbers or dense ones would otherwise classify the type a second time, and two classifications
     * of one type are two chances to disagree.
     *
     * <p>Every number the language calls one, today: the domain holds a scalar, and a value the
     * language compares as a number is one it can hold. The two are answered by one call for that
     * reason and not because they are one question — an equality reaches values no domain carries,
     * and a type being comparable is no promise that an affine domain can hold it. Where those come
     * apart this stops delegating; until then the delegation is what says why the answers agree.
     *
     * <p>Remembered by the type it names — asked at every leaf of every affine walk, and answering it
     * walks the declaration's fields.
     */
    Type affineScalarBase(Type t) {
        if (t == Type.INT || t == Type.DECIMAL) {
            return t;
        }
        if (!(t instanceof Type.Ref ref)) {
            return TypeOps.numericBase(t, symbols);
        }
        return affineScalarBases.computeIfAbsent(ref.name(),
                _ -> java.util.Optional.ofNullable(TypeOps.numericBase(t, symbols)))
                .orElse(null);
    }


    static boolean isArith(Hir.BinOp op) {
        return op == Hir.BinOp.ADD || op == Hir.BinOp.SUB || op == Hir.BinOp.MUL || op == Hir.BinOp.DIV;
    }
    /** How a preserved call's operation is reached: it is the library's, named under the alias the
     * library publishes it under. */
    private static ReachName reachOf(ValueName operation) {
        return new ReachName.OfLibrary((ValueName.Stdlib) operation);
    }

}
