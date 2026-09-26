package souther.compiler.core;

import souther.compiler.types.BinOp;
import souther.compiler.types.BindingId;
import souther.compiler.types.CaseSelector;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.MaterialisationSite;
import souther.compiler.types.OccurrenceLineage;
import souther.compiler.types.ApplicationOrigin;
import souther.compiler.types.ReferenceOrigin;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.Refinement;
import souther.compiler.types.ReachName;
import souther.compiler.types.ResolvedCase;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;
import souther.compiler.diag.SourcePos;
import souther.compiler.regex.PatternMeaning;

import java.math.BigDecimal;
import java.util.List;
import java.util.Objects;
import java.util.Optional;

/**
 * The Core IR (ADR-0021): a checked executable expression, which is what every backend emits from.
 *
 * <p>Three things the language states reach a backend as this — a behavior's or a {@code let}'s
 * body, a data's {@code invariant} condition, and the rule an {@code ensures} states — and each is
 * the written expression with the helpers it names inlined and the surface-only forms desugared. It
 * differs from the AST in what it makes explicit: a construct the backend used to re-detect and
 * shape during emission becomes its own node here, so the backend only emits.
 *
 * <p>Every node carries {@link #type()}: the type the checker decided for it (issue #81). The
 * checker is the only one that decides a type — it builds the tree as it types what was written
 * ({@code Elaborator.elaborate}) — so the backend reads those decisions instead of deciding them a
 * second time. A pass after checking ({@link GrowingFold}) rebuilds the tree it is handed, and what
 * it puts there is either a decision it was handed or one its own rewrite determines, such as the
 * type a binding is in force at once the list it stood for is no longer built. A {@link Widen} such
 * a pass puts there restates one the checker decided, and never relates two types the checker did
 * not. A condition was the exception until #1080, and being the exception meant the last
 * step of deciding what a clause meant sat inside a backend.
 *
 * <p>A name in a body is one of two nodes, not one: a read of something the body binds, and a unit
 * data written as its own value. They were one, and the emitter told them apart by looking the
 * spelling up in its slots and falling back when it found nothing — which is an answer about a
 * name, decided by its text.
 *
 * <p>A surface-only node (a list comprehension) never appears — it is desugared before the
 * elaboration that produces this, whether what is being read is a body or a clause.
 */
public sealed interface Core {

    SourcePos pos();

    /** The type the checker decided for this expression. */
    Type type();

    record Int(long value, Type type, SourcePos pos) implements Core {}

    record Decimal(BigDecimal value, Type type, SourcePos pos) implements Core {}

    record Str(String value, Type type, SourcePos pos) implements Core {}

    record Bool(boolean value, Type type, SourcePos pos) implements Core {}

    /**
     * A temporal written out: {@code Date("2026-07-01")}, {@code Time("09:00")},
     * {@code DateTime("2026-07-01T09:00")}, {@code Instant("2026-07-01T09:00:00Z")}.
     *
     * <p>A literal, and here beside the other four for the reason the language calls it one
     * (spec §a-temporal-value-is-written-as-a-literal): the text is written where the value goes,
     * and the checker has already read it. It was carried this far as a {@link Call} instead, which
     * is the shape an application has — so every reader that needed to know a written temporal from
     * a call had to work it out, and each took a different thing to work it out from: the spelling
     * in front of the argument, the type the call answered, the shape of the argument. A model
     * declaring a behavior of its own named {@code Date} was compiled as this construction, its
     * injected implementation never called. None of them is a question this node can be asked.
     *
     * <p>{@code kind} is the temporal, and the node's type is it: one value, so the two cannot
     * disagree. {@code text} is the ISO text as it was written, which is what a reader of this wants
     * — the backend parses it, a boundary reads its place — and the parse the checker already did is
     * what says the text is good.
     */
    record Temporal(Type.Prim kind, String text, ApplicationOrigin application, SourcePos pos)
            implements Core {

        // `application` is the construction this was written as, kept because the fold is where a
        // root goes missing. A temporal reaches here as the value it denotes rather than as the
        // construction it was spelled with, and what is folded away is the application — not which
        // one it was. A reader below writing the construction back out has this to write it from,
        // and the place could not answer for it: one helper is expanded at several of its calls.
        //
        // The application and not the name inside it. What a temporal's construction names is a
        // namespace rather than a declaration, and a namespace is not a thing to be a reference of,
        // so there is no second occurrence here to keep.

        public Temporal {
            if (kind == null || !kind.temporal()) {
                throw new IllegalArgumentException("`" + kind + "` is no temporal");
            }
            if (text == null) {
                throw new IllegalArgumentException("a written temporal is written out");
            }
            // A temporal reaches here having been written as a construction, so there is one to
            // name. A reader below writes the construction back out from this and has nowhere else
            // to get it.
            if (application == null) {
                throw new IllegalArgumentException(
                        "a written temporal was written as some construction: " + text);
            }
        }

        @Override
        public Type type() {
            return kind;
        }
    }

    /**
     * A binding this tree makes: a {@code let}, a lambda's parameter, a {@code match} arm's name.
     *
     * <p>Core's own, and not the resolved tree's binder. What the binder itself holds is which
     * binding it is and what to call the local — the two here. The type the binding is in force at
     * is not among them: the node that makes the binding answers it ({@link LetIn#bindType}, a
     * {@link Block}'s {@link Type.FnOf} parameters, a {@link Case}'s pattern), and a binder
     * carrying it too would state that fact twice. The rest of a resolved binder is about
     * the characters an author typed: the spelling before a desugaring canonicalised it, and where
     * the name was written, which is what a cursor is compared against. A backend has no cursor and
     * emits no spelling, and Core naming that form put {@code souther.compiler.ast} on what a
     * backend outside this compiler reads.
     *
     * <p>One spelling for the binding. The resolved binder answers it as both {@code binding()} and
     * {@code id()}, and a reader that has to pick between two names for one thing is a reader that
     * can be read two ways.
     */
    record Binder(String name, BindingId binding) {

        @Override
        public String toString() {
            return name;
        }
    }

    /**
     * Where a fork of the model stands: which fork the source wrote and which copy of it this is
     * ({@code occurrence}), and what that copy is called where the rules a call supplied are looked
     * up ({@code expansion}), innermost first.
     *
     * <p>One value because neither is true without the other. A fork is a construct the model owes
     * coverage for and a copy the inliner made, and a reader that has one of the two is a reader
     * that files one fork under another's name — so there is no fork here with an occurrence and no
     * lineage, and none with a lineage and no occurrence.
     *
     * <p>The expansion is empty where the fork stands in the body as the author wrote it, which is a
     * fork of the model in no copy but its own. That is a thing to say, and it is why the two are a
     * product rather than one value derived from the other: which construct a copy is of is settled
     * by the calls the source wrote, and what a binding belongs to is the inlining pass's own
     * answer, which is what the table of supplied rules is keyed by.
     */
    record ForkPlace(ConstructOccurrence occurrence,
                     List<souther.compiler.types.BindingOwner> expansion) {

        public ForkPlace {
            if (occurrence == null) {
                throw new IllegalArgumentException(
                        "a fork is some fork of the model, in some copy of the body that wrote it");
            }
            expansion = List.copyOf(expansion);
        }

        /** A fork standing in the body as it was written, which is in no copy but its own. */
        public static ForkPlace asWritten(ConstructOccurrence occurrence) {
            return new ForkPlace(occurrence, List.of());
        }
    }

    /**
     * Where a call a representation kept standing stands: which occurrence of the operation's name
     * it applies ({@code reference}) and why the application is here ({@code application}).
     *
     * <p>Two questions and one value. The block a name used as a value was expanded into holds an
     * application this compiler wrote applying a name the author wrote, so neither answers the
     * other; and a reader writing the call back out has to name a name and compose an application,
     * so it wants both. One of them alone is half a call, which is a state no producer means and
     * the first reader to meet one would be reporting somebody else's mistake.
     */
    record KeptCallPlace(ReferenceOrigin reference, ApplicationOrigin application,
                         OccurrenceLineage lineage) {

        public KeptCallPlace {
            if (reference == null || application == null || lineage == null) {
                throw new IllegalArgumentException("a call carries what it applies, why it is"
                        + " here and which copy it stands in: " + reference + " and "
                        + application);
            }
        }
    }

    /** A read of something the body binds: a parameter, a {@code let}, a lambda's parameter, a
     * {@code match} arm's binding. {@code binding} is which one; {@code name} is what to call the
     * local it is emitted as, and what a diagnostic quotes. */
    record Read(String name, BindingId binding, Type type, SourcePos pos) implements Core {}

    /** A unit data written where a value goes: the type has one value, and naming it is that value
     * (spec §unit-data). Which unit is on the node, so nothing resolves a spelling again. */
    record UnitValue(TypeSymbol data, Type type, SourcePos pos) implements Core {}

    /**
     * A build of a value in the tree an analysis reads: where the value is evaluated, and not what it
     * means.
     *
     * <p>What the value means is its template, held once for the whole of what reads this tree and
     * asked of it by {@code value}. A tree that held the body at every build would hold a copy per
     * region that builds it, and values naming one another in several regions would grow with every
     * link. Nothing here is a call: there is nothing applied and nothing passed, and a reader that
     * walks a node's children meets no body under it.
     *
     * @param value which value, by the name the module reaches it by
     * @param site  the region this build stands in
     */
    record MaterialisedValue(ReachName.Declaration value, MaterialisationSite site, Type type,
                             SourcePos pos) implements Core {}

    record Neg(Core operand, Type type, SourcePos pos) implements Core {}

    record FieldAccess(Core target, String field, Type type, SourcePos pos) implements Core {}

    /**
     * {@code occurrence} is which comparison of the model this is: the construct the source wrote
     * (see {@link souther.compiler.ast.Hir.Binary}) and the copy of the body it stands in. Both,
     * because a helper spliced into two calls holds one written comparison twice, and a reader
     * holding only the first would be reading one of them about the other.
     *
     * <p>{@code reading} is what the operator reads its operands as, which the checker settled and
     * the three types here do not say. {@code type} is what the operator answers, and the two differ:
     * {@code i / j} over two {@code Int}s reads them as they stand and answers a {@code Rational}.
     */
    record Binary(BinOp op, Core left, Core right, BinaryReading reading,
                  ConstructOccurrence occurrence, Type type, SourcePos pos) implements Core {

        public Binary {
            // A comparison is some comparison of the model, in some copy of the body that wrote it.
            // Both halves are the occurrence's to say, and a comparison that is neither is one no
            // reading of coverage can file.
            if (occurrence == null) {
                throw new IllegalArgumentException(
                        "a comparison is some comparison of the model: " + op);
            }
            if (reading == null) {
                throw new IllegalArgumentException("an operator reads its operands as something: "
                        + op);
            }
            if (reading instanceof BinaryReading.AsTheyStand
                    && !left.type().equals(right.type())) {
                throw new IllegalArgumentException("operands read as they stand stand as one type: "
                        + left.type() + " " + op + " " + right.type());
            }
        }

        /** What the source wrote, for a reader whose question is about the construct alone. */
        public SourceConstructOrigin origin() {
            return occurrence.origin();
        }
    }

    /**
     * What an operator reads its two operands as, as the checker settled it.
     *
     * <p>Not a type of either operand and not a place either stands: an {@code Int} beside a
     * {@code Rational} is still refused where a Rational is asked for, and a literal beside a
     * newtype is read as the newtype by this operator and by nothing else. That is why this is not a
     * {@link Widen}. And not which rule of the checker allowed it: a reading says what the operands
     * were taken as, which is what a backend lowers, and two rules that settle on one reading are
     * one reading here.
     *
     * <p>Newtype arithmetic has none of its own. The tree already says it — each operand opened to
     * what it wraps, the operation over those, the result built again — and the operation inside
     * reads its numbers as they stand.
     *
     * <p>Every one of these reads the two sides alike, so a comparison turned round keeps it.
     */
    sealed interface BinaryReading {

        /** Each operand as the type it has, which is one type for both. */
        record AsTheyStand() implements BinaryReading {}

        /**
         * The pair as values of {@code type}, for this operator only: a literal beside the newtype it
         * is compared with, a case beside the enumeration that orders it, two values tested for
         * sameness across one set of cases, a value beside one that states nothing about its own
         * type.
         *
         * <p>Never which side came first: what an operator reads its operands as is the same
         * written either way round, so the type is one both sides settle and not one of theirs
         * picked. Where two sides name one set of cases, it is that set as a union.
         */
        record In(Type type) implements BinaryReading {
            public In {
                if (type == null) {
                    throw new IllegalArgumentException("a pair is read in some type");
                }
            }
        }

        /** Each operand at its exact mathematical value, which one of them already being a
         *  {@code Rational} makes of the pair (ADR-0116). No type of the language stands for it. */
        record ExactNumbers() implements BinaryReading {}

        AsTheyStand AS_THEY_STAND = new AsTheyStand();

        ExactNumbers EXACT_NUMBERS = new ExactNumbers();
    }

    /**
     * What a call applies.
     *
     * <p>Two things reach this far and they are not the same kind of thing. One is a callee some
     * module named, which resolution answered and the tree carried here. The other is an operation
     * this compiler emits and no source can write: a Core-to-Core pass mints it after everything has
     * been resolved and type-checked, and it stands for a shape the backend knows how to lower.
     *
     * <p>They are held apart because a {@link ReachName} is the name a module reaches a definition
     * by, and an operation nothing declares is not that. Written as one, the type would say a name
     * had been resolved where nothing resolved it — which is the confusion the reach name was
     * separated out to end.
     */
    sealed interface CallTarget {

        /** What a report quotes and, for a call the backend emits as a method, what the method is
         * named after. */
        String rendered();
    }

    /**
     * A callee some module named: the reference resolution settled for it.
     *
     * <p>One value, because a reference is one. The backend emits the method the reach name spells;
     * a reader asking what kind of thing was called — a module's own helper, one of the language's
     * operations, a behavior whose implementation comes from outside — asks what that reference
     * denotes, and {@link ReachName} carries both. Held as a route and a denotation side by side,
     * the two could be paired from different references and nothing would say so.
     *
     * <p>A kernel call is one of these and not something beside them. {@code List.sort} is reached
     * by a name and resolves to a library operation, and its declaration being a kernel is what that
     * operation turned out to be — so a reader asking what a call reaches asks this, whichever arm
     * it is, and only a reader that has to emit the operation goes on to ask which kernel. Put
     * beside {@code Reached}, the arms would divide by provenance for two of them and by what the
     * declaration holds for the third, and a reader that wanted only the name would stop seeing
     * kernels without being told.
     */
    sealed interface Reached extends CallTarget {

        /** The reference the module being emitted reaches the callee by, which reaches a
         *  declaration — a call is emitted for nothing else, and both arms below say so. */
        ReachName.Declaration name();

        /** What that reference reaches. Read off the reference rather than held beside it: a
         *  declaration kept next to the route it was reached by is the same fact twice, and the two
         *  agree only until a pass replaces one of them. */
        default ValueName denotes() {
            return name().denotes();
        }

        @Override
        default String rendered() {
            return name().rendered();
        }

        /**
         * A callee whose declaration this compilation carries: a helper the emitting module holds
         * as a method of its own, or a behavior. What is emitted for it is a call.
         *
         * <p>Those two and nothing else, said here rather than found out downstream. A binding is
         * applied where it stands and a type used as a value is a construction, so neither is a
         * call to a declaration; a library operation the language implements is a kernel and is
         * {@link OfKernel}. An emitter reading one of these divides it into a helper and a behavior
         * and has no third arm to write, and that is true because this refuses to build a fourth
         * rather than because the emitters have all been counted.
         */
        record OfDeclaration(ReachName.Declaration name) implements Reached {

            /**
             * What running this call means: a method of the emitting module, or a behavior.
             *
             * <p>Derived and not held. What a call reaches is on the reference already, and the two
             * kinds of thing a residual call can reach are the arms this refuses to be built with —
             * so an emitter reading this is reading the reference rather than a second answer that
             * could come to disagree with it.
             *
             * <p>Not a property of a {@link ValueName}. Whether the library implements an operation
             * as a helper, an intrinsic or a builtin is the library's own business and is
             * deliberately not on the name; what holds here is narrower — that a call this
             * compilation kept standing over a library operation is a call to a method, because a
             * kernel would be {@link OfKernel} and anything else would have been expanded. That is
             * true of this phase and is said at this phase.
             */
            public Reaches reaches() {
                return switch (name) {
                    // A helper of this module and one of another are the same thing to emit: a call
                    // to a method the module holds. So is an operation the library wrote in
                    // Souther — what differs between the three is where the declaration came from,
                    // which is a different question and is asked of the declaration.
                    case ReachName.Own(ValueName.OfAModule declared) -> ofAModule(declared);
                    case ReachName.OfModule(ValueName.OfAModule declared) -> ofAModule(declared);
                    case ReachName.OfLibrary(ValueName.Stdlib.Operation operation) ->
                            new Reaches.AHelper(operation);
                };
            }

            private static Reaches ofAModule(ValueName.OfAModule declared) {
                return switch (declared) {
                    case ValueName.Helper helper -> new Reaches.AHelper(helper);
                    case ValueName.Behavior behavior -> new Reaches.ABehavior(behavior);
                };
            }

            public OfDeclaration {
                if (name == null) {
                    throw new IllegalArgumentException(
                            "a call applies something this compilation resolved");
                }
            }

            @Override
            public String toString() {
                return rendered();
            }
        }

        /**
         * A value the emitting module declares, built where the tree that runs names it.
         *
         * <p>Its own family and not an {@link OfDeclaration}. A value is not a helper: it runs in the
         * one place its module builds it, and what it answers lives past the call that reads it,
         * where a helper's method is a copy a call was left standing to. What is emitted for it is a
         * call to the method the module runs the value as, handed the values its root region
         * demands.
         */
        record OfValue(ReachName.Declaration name) implements Reached {

            public OfValue {
                if (name == null || !(name.denotes() instanceof ValueName.Helper)) {
                    throw new IllegalArgumentException(
                            "a value is a helper of the module that declares it: " + name);
                }
            }

            /** What running this call means: the method the value runs as. */
            public Reaches reaches() {
                return new Reaches.AValue((ValueName.Helper) name.denotes());
            }

            @Override
            public String toString() {
                return rendered();
            }
        }

        /**
         * A value another module publishes, read where it is named.
         *
         * <p>Its own family and not an {@link OfDeclaration}, because what is emitted for it is not a
         * method this module holds. The value has one place it runs, which is the module that
         * declares it, and this module calls that module's entry for it — so nothing of the value's
         * body, and nothing of the types the body is built from, is this module's to know.
         */
        record OfPublishedValue(ReachName.OfModule name) implements Reached {

            public OfPublishedValue {
                if (!(name.denotes() instanceof ValueName.Helper)) {
                    throw new IllegalArgumentException(
                            "a published value is a helper of the module that declares it: " + name);
                }
            }

            /** What running this call means: the entry its declaring module publishes. */
            public Reaches reaches() {
                return new Reaches.APublishedValue((ValueName.Helper) name.denotes());
            }

            @Override
            public String toString() {
                return rendered();
            }
        }

        /**
         * A callee whose declaration is a kernel of the standard library, and which kernel it is.
         *
         * <p>Which kernel is the answer to a question this compiler settled: the checker typed the
         * call against the library's signature, and the declaration behind that signature named the
         * operation. An output reads the operation here rather than going back to a table this
         * compiler keeps for itself — and a spelling it guessed from would be resolving, by the
         * alias and the name, what was resolved already.
         *
         * <p>The kernel is beside the reference and is not part of it. The reference says how this
         * module got here and which declaration it chose; the kernel says what that declaration
         * turned out to be, which the library answered and this holds rather than asks again. Two
         * declarations naming one kernel is a thing the library is refused for while it is built,
         * not a thing this collapses.
         */
        record OfKernel(ReachName.OfLibrary name, Kernel kernel) implements Reached {

            public OfKernel {
                // Only the library declares a kernel, and only an operation of it is one. Both are
                // the type of the reference, so there is nothing here to turn away.
                if (name == null) {
                    throw new IllegalArgumentException("a kernel call reaches the operation it is");
                }
            }

            @Override
            public String toString() {
                return rendered();
            }
        }
    }

    /**
     * What a call to a declaration runs, for whoever has to emit it.
     *
     * <p>The kinds of thing a call that survived to here can reach, and the division an emitter
     * writes its arms over. Not provenance: a module's own helper, another module's and a library
     * operation written in Souther are one answer, because one thing is emitted for all three — a
     * call to a method the emitting module holds. What differs between them is where the
     * declaration came from, which is a different question and is asked of the declaration. A value
     * is a different answer and not a different provenance: it runs in the one place its module
     * builds it, and lives past the call that reads it.
     *
     * <p>Read off a call rather than stored on one ({@link Reached.OfDeclaration#reaches}), so this
     * cannot come to say something the reference does not.
     *
     * <p>Sealed, and the switches over it carry no {@code default}: another kind of callee is a
     * compile error at every emitter rather than a call one of them quietly does nothing for.
     */
    sealed interface Reaches {

        /** The declaration reached. */
        ValueName declaration();

        /**
         * A method the emitting module holds, which is where this program's recursions live.
         *
         * <p>{@code declaration} is what the module holds a copy of, and which module wrote it is
         * that identity's to say — {@code souther.list} for an operation reached as
         * {@code List.foldFrom}. Where the module holds the method is not here: that follows from
         * how the call reaches it, and a reader emitting one works it out from the reference.
         */
        record AHelper(ValueName declaration) implements Reaches { }

        /**
         * A value the emitting module declares, which runs here and nowhere else. What is emitted is
         * a call to the method the module runs it as.
         */
        record AValue(ValueName.Helper value) implements Reaches {

            @Override
            public ValueName declaration() {
                return value;
            }
        }

        /**
         * A value another module declares, which runs there. What is emitted is a call to the
         * public entry that module publishes for it, and never a method of the emitting module.
         */
        record APublishedValue(ValueName.Helper value) implements Reaches {

            @Override
            public ValueName declaration() {
                return value;
            }
        }

        /**
         * A behavior, whose implementation is somewhere else — another module's, or supplied from
         * outside this program altogether.
         *
         * <p>Where the value of it stands when this call runs is the emitter's own question: a
         * field of the class being emitted, a parameter, a slot. That is a fact about how one
         * output lays a frame out and is no part of what the call reaches.
         */
        record ABehavior(ValueName.Behavior behavior) implements Reaches {

            @Override
            public ValueName declaration() {
                return behavior;
            }
        }
    }

    /**
     * An operation this compiler emits, which no source names and no module declares.
     *
     * <p>Each is minted by a Core-to-Core pass ({@link GrowingFold}) for a shape the backend lowers
     * as a whole. The backend matches on the operation rather than on a spelling of it; what it
     * renders as is for a report to quote.
     */
    enum Emitted implements CallTarget {

        /** {@code $build(step, xs, from)} — the walk that grows a list into a builder and seals it. */
        BUILD_LIST("List.$build"),
        /** The {@code acc ++ …} inside a rewritten step, adding to the builder the walk carries. */
        GROW_LIST("List.$grow"),
        /** The same walk for a fold accumulating a map. */
        BUILD_MAP("Map.$build"),
        /** The step's write into the map builder. */
        PUT_MAP("Map.$put");

        private final String rendered;

        Emitted(String rendered) {
            this.rendered = rendered;
        }

        @Override
        public String rendered() {
            return rendered;
        }

        @Override
        public String toString() {
            return rendered;
        }
    }

    /**
     * What the checker settled about one application beyond its type, carried on the {@link Call}
     * it was settled for rather than derived from its arguments a second time downstream.
     *
     * <p>A kernel's signature ({@link KernelSignature}) is declared once with type variables, and
     * each application settles them: what that application takes each argument as is the checker's
     * answer, and an output reading it off here does not substitute the signature again under a rule
     * of its own. A call to anything else may settle variables of its declaration too — a recursive
     * helper such as {@code List.foldFrom} is declared over {@code 'acc} — but carries nothing
     * here for it: each argument stands as what the application settled it takes that argument as,
     * and the call is of what it settled it answers, so the settlement is already in the call's
     * arguments and type. {@link None} says there is nothing further, not that nothing was settled.
     *
     * <p>Sealed on purpose: a fact belongs here because the checker settled it about one application
     * and it became part of that application's meaning, not because some pass found it convenient to
     * stash. A {@code Map<String, Object>} would accept whatever a later pass wanted to put there,
     * and a reader could no longer tell a settlement the checker stands behind from one pass's scratch
     * space.
     */
    sealed interface CallSettlement {

        /** A call that is no kernel's application, so nothing about it is carried beyond what its
         *  arguments and its type already say. */
        enum None implements CallSettlement {
            INSTANCE
        }

        /**
         * One application of a kernel: what it takes each of its arguments as, and whatever else the
         * checker settled about it ({@link KernelFact}).
         *
         * <p>{@code takes} is the kernel's declared parameters under the substitution the checker
         * settled for this application, and never the arguments' own types read back: the call
         * holds each argument at exactly that type, which is a statement only while the two come
         * from different places. What the application answers is the call's type, and not held a
         * second time here.
         */
        record AtKernel(List<Type> takes, KernelFact fact) implements CallSettlement {

            public AtKernel {
                takes = List.copyOf(takes);
                Objects.requireNonNull(fact, "a kernel's application carries its fact, `None` where"
                        + " there is none");
            }
        }
    }

    /**
     * A fact the checker settled about one kernel's application, beside what it takes its arguments
     * as.
     */
    sealed interface KernelFact {

        /** The checker settled nothing about this application beyond what it takes and answers. */
        enum None implements KernelFact {
            INSTANCE
        }

        /**
         * What the pattern of {@code String.matches} means, read where the call was checked.
         *
         * <p>The checker folds the first argument under the bindings in force and reads the text it
         * comes to as a pattern of the language (spec §string-patterns); the call exists only where
         * that reading is a pattern. What an output lowers is {@code meaning}, so no output reads
         * pattern text, and every output answers for the strings the checker read the pattern as.
         *
         * @param written the text the argument folds to, as the author wrote it. Provenance only: an
         *                output may quote it and never reads it as a pattern
         * @param meaning which strings the pattern accepts
         */
        record StringMatches(String written, PatternMeaning meaning) implements KernelFact {

            public StringMatches {
                Objects.requireNonNull(written, "a settled pattern is settled from some text");
                Objects.requireNonNull(meaning, "a settled pattern means some set of strings");
            }
        }

        /** The {@link Type} an ordering requirement was checked against for one application of
         * {@code List.sort}, {@code List.max}, {@code List.min}, or {@code List.sortBy} — the list's
         * element for the first three, the sort key's result for the last. Not always a Type proved
         * ordered: the requirement holds it just as readily where there was nothing yet to check —
         * {@code Nothing} for an empty-list literal, a still-open type variable, or bottom — as where
         * the Type does support ordering. A Type the requirement refused never reaches here; that is
         * a compile error instead. Never a comparator, method symbol, or other backend
         * representation: a backend reads {@link #type()} and decides its own representation from
         * it. */
        record OrderingSubject(Type type) implements KernelFact {

            public OrderingSubject {
                Objects.requireNonNull(type, "a settled ordering subject is settled to some type");
            }
        }
    }

    /**
     * A call to a builtin, an injected behavior, an intrinsic, or a recursive helper emitted as a
     * method — none of them bound by this body. A non-recursive helper is already inlined.
     *
     * <p>{@code fn} says what is applied ({@link CallTarget}). Where that is a name, it is the one
     * the module being emitted reaches the callee by, carried from where resolution settled it, and
     * held as what it is rather than as the spelling of it: the backend needs the whole name to emit
     * the method it calls, and what the name denotes to know what kind of thing was called. Where
     * the callee turned out to be a kernel of the standard library, the call says which one
     * ({@link Reached.OfKernel}), so an output emitting it asks the call rather than this compiler.
     *
     * <p>{@code settlement} is a fact the checker proved about this one application beyond its type
     * ({@link CallSettlement}) — never a rewrite of {@code args}. What a body evaluates at run time
     * and what the checker proved about it at compile time are different questions, and folding the
     * second into the first would lose the tree a rewrite, an occurrence or a coverage obligation
     * still reads.
     *
     * <p>A kernel's application says what it takes each argument as, and each argument is of
     * exactly that type — a {@link Widen} where the value is narrower. Held here as equality and not
     * as whether one may stand as the other: that was decided where the Widen was placed. A rewrite
     * that changes an argument's type without settling the application again is refused here rather
     * than carried on to an output that would read the two as disagreeing.
     */
    record Call(CallTarget fn, List<Core> args, ConstructOccurrence occurrence,
                CallSettlement settlement, Type type, SourcePos pos) implements Core {

        public Call {
            // A call is some call of the model, in some copy of the body that wrote it — or one no
            // source wrote, which says so. A call that is neither is one no reader can file, and a
            // reader that meets it has nothing to send an author to.
            if (occurrence == null) {
                throw new IllegalArgumentException(
                        "a call is some call of the model: " + fn.rendered());
            }
            // `None` where the checker settled nothing, rather than left unstated: a reader asking
            // whether this call has a settlement gets one answer either way, never an absent field.
            if (settlement == null) {
                throw new IllegalArgumentException(
                        "a call carries its settlement, `None` where there is none: " + fn.rendered());
            }
            // Which kind of call owns a settlement is asked of the settlement, exhaustively and with
            // no `default`: a case added later to `CallSettlement` or `KernelFact` without a line
            // here is a compile error at this constructor, not a call this refuses to notice was
            // ever handed one. An `instanceof` of one arm compared as a boolean would answer the same
            // for every case this has not been told about yet, which is the failure mode this switch
            // is here to refuse.
            boolean agrees = switch (settlement) {
                case CallSettlement.None _ -> !(fn instanceof Reached.OfKernel);
                case CallSettlement.AtKernel(_, KernelFact fact) ->
                        fn instanceof Reached.OfKernel(_, Kernel kernel) && factAgrees(kernel, fact);
            };
            if (!agrees) {
                throw new IllegalArgumentException("`" + fn.rendered() + "` and its settlement "
                        + settlement + " disagree about what kind of call this is");
            }
            if (settlement instanceof CallSettlement.AtKernel(List<Type> takes, _)) {
                if (takes.size() != args.size()) {
                    throw new IllegalArgumentException("`" + fn.rendered() + "` takes "
                            + takes.size() + " argument(s) and is handed " + args.size());
                }
                for (int i = 0; i < args.size(); i++) {
                    if (!takes.get(i).equals(args.get(i).type())) {
                        throw new IllegalArgumentException("argument " + (i + 1) + " of `"
                                + fn.rendered() + "` stands as " + Type.show(args.get(i).type())
                                + " where the application takes it as " + Type.show(takes.get(i)));
                    }
                }
            }
        }

        /**
         * Whether {@code fact} is one {@code kernel}'s application can carry. {@code String.matches}
         * carries its pattern and nothing else, and no other kernel carries a pattern. Which kernels
         * carry an ordering subject is the checker's to decide and not a second table held here:
         * this asks only that it is not {@code String.matches}, which has its own.
         */
        private static boolean factAgrees(Kernel kernel, KernelFact fact) {
            return switch (fact) {
                case KernelFact.None _ -> kernel != Kernel.STRING_MATCHES;
                case KernelFact.StringMatches _ -> kernel == Kernel.STRING_MATCHES;
                case KernelFact.OrderingSubject _ -> kernel != Kernel.STRING_MATCHES;
            };
        }

        /** The callee as it renders — the reach name for a call to one, the operation's own
         * spelling for one this compiler emits. What a method name is built from and what a report
         * quotes; never what a source wrote. */
        public String name() {
            return fn.rendered();
        }

        /** What the source wrote, for a reader whose question is about the construct alone. */
        public SourceConstructOrigin origin() {
            return occurrence.origin();
        }

        /** What emitting a call does with a function it is handed. */
        public enum FunctionArgument {
            /** Run as the loop body: no class is made for it, and what it closes over is read from
             *  the frame around it. */
            RUNS_WHERE_IT_STANDS,
            /** Never applied, so {@code Fn.NEVER} is handed over in its place and none of it — no
             *  class, no body — is emitted. */
            NEVER_APPLIED,
            /** Handed over as a value: a class with a field for each thing it closes over. */
            HANDED_OVER
        }

        /**
         * What emitting this call does with the function at {@code index}.
         *
         * <p>A method is handed a function that is never applied as {@code Fn.NEVER}, and a kernel's
         * row hands the runtime the function it is given whatever it is. The one answer, read by the
         * emitter and by whatever asks which classes an emitted call names, so the two do not come to
         * disagree about which of the three a function is.
         *
         * @param theWalk what the standard library's one loop is called
         */
        public FunctionArgument functionArgument(int index, ValueName theWalk) {
            if (!(args.get(index).type() instanceof Type.FnOf fnType)) {
                throw new IllegalArgumentException("argument " + index + " of `" + fn.rendered()
                        + "` is not a function");
            }
            if (index == 0 && stepRunWhereItStands(theWalk) != null) {
                return FunctionArgument.RUNS_WHERE_IT_STANDS;
            }
            return !(fn instanceof Reached.OfKernel) && neverRuns(fnType)
                    ? FunctionArgument.NEVER_APPLIED : FunctionArgument.HANDED_OVER;
        }

        /**
         * The step this call runs where it stands, as the loop it is, or null where it does not: the
         * step is handed over as a function, or replaced by {@code Fn.NEVER} because it is never
         * applied ({@link #functionArgument} says which).
         *
         * <p>A walk that starts at the head of the list, and a build of a list or a map, run their
         * step as the loop body, reading what it closes over from the frame around it: no class is
         * made for it, and no method is called, so nothing comes back to be cast to the type the
         * call answers.
         *
         * @param theWalk what the standard library's one loop is called
         */
        public Block stepRunWhereItStands(ValueName theWalk) {
            boolean walks = fn == Emitted.BUILD_LIST || fn == Emitted.BUILD_MAP
                    || (fn instanceof Reached reached && theWalk.equals(reached.denotes())
                    && args.size() > 3 && withoutStanding(args.get(3)) instanceof Int from
                    && from.value() == 0);
            return walks ? runsWhereItStands(args.get(0)) : null;
        }
    }

    /**
     * {@code step} as a block that is run where it stands, or null where it is not one: not a block
     * at all, or a step that would never be applied because an element of it has no type to be.
     */
    static Block runsWhereItStands(Core step) {
        return withoutStanding(step) instanceof Block block && !neverRuns(block.type())
                ? block : null;
    }

    /**
     * Whether a step closure would never be applied: one of its parameters is the bare bottom, so
     * it is the element of an empty-literal list and there are no elements — {@code foldFrom} over
     * {@code []} yields the seed. Such a step is passed as {@code Fn.NEVER} rather than materialised,
     * since materialising it would unbox the bottom element (as {@code acc + x} does with {@code x})
     * and crash. An empty *seed* (a {@code List<Nothing>} accumulator) is a reference and still
     * materialises.
     */
    static boolean neverRuns(Type.FnOf step) {
        for (Type p : step.params()) {
            if (p instanceof Type.Nothing) {
                return true;
            }
        }
        return false;
    }

    /**
     * A name a representation kept standing on purpose: resolved to the declaration it names, typed
     * from what that declaration settled, and deliberately not expanded. A call is one, with its
     * arguments; a reference to a value is one with none, since reading a value's name is running
     * its body (ADR-0072) and a representation that did not substitute it kept that.
     *
     * <p>Not a call this compiler failed to expand. Which calls survive is a representation's to
     * decide ({@link souther.compiler.check.InliningPolicy}): an analysis that has rules about an
     * operation loses them the moment the operation becomes the algorithm it is, so the
     * representation that analysis reads keeps the operation. The tree the backend emits from keeps
     * none, and one arriving there is this compiler having failed to expand it.
     *
     * <p>{@code declared} is what the name was resolved to, read against the declaration it reaches
     * — not how it was written: two spellings that reach one operation are one of these, and having
     * a type in common is not being the same operation. A reader with no rule for what this names
     * types it and learns nothing from it, which is the difference between a representation keeping
     * a call and an analysis understanding one.
     *
     * <p><b>Its arguments are the ones that declaration takes.</b> Said here because it is a fact
     * about the node and not about whoever built one: a reader that finds an argument by a position
     * some rule about the operation names is reading a position the declaration has. The operation
     * and the arguments are one component and a list beside it, so that the two cannot be paired
     * from different declarations — what may say that a name has been read against a declaration is
     * {@link CompleteSignature} and nothing else.
     */
    record PreservedCall(DeclaredOperation declared, List<Core> args, KeptCallPlace place,
                         Type type, SourcePos pos) implements Core {

        // Not a construct of the source. A call kept for a reader to quote is not always one an
        // author wrote: a library operation used as a value is expanded into a block, and the
        // application inside that block is kept in the same way. Held as a construct, those arrived
        // saying no source wrote them and nothing said what they were instead.

        /** Which occurrence of the operation's name this applies. */
        public ReferenceOrigin reference() {
            return place.reference();
        }

        /** Why this application is here. */
        public ApplicationOrigin application() {
            return place.application();
        }

        /**
         * Which call of the model this is, in the copy of the body that wrote it.
         *
         * <p>Read off the two halves already here rather than held beside them: which construct it
         * is, is what the application says where an author wrote one, and which copy it stands in
         * is the place's. Held as a third component, the construct would be written down twice and
         * the two could come apart.
         *
         * <p>Nothing for an application no author wrote — a name read as a value, a size a pass
         * composed — which is what {@link ConstructOccurrence#unwritten()} says. A reader sent to
         * one of those would be pointed at something nobody can edit.
         */
        public ConstructOccurrence occurrence() {
            return place.application()
                    instanceof ApplicationOrigin.Written(SourceConstructOrigin wrote)
                    ? new ConstructOccurrence(wrote, place.lineage())
                    : ConstructOccurrence.unwritten();
        }

        public PreservedCall {
            if (place == null) {
                throw new IllegalArgumentException("a call kept standing stands somewhere: it"
                        + " applies some occurrence of a name, for some reason: " + declared);
            }
            // Taken over rather than borrowed. Checking a list the caller goes on holding says what
            // was true when the call was built, and every reader below reads the call afterwards —
            // a pass that kept the list it handed over could put another argument in it and leave a
            // node behind whose own statement about itself had stopped being true.
            args = List.copyOf(args);
            if (args.size() != declared.arity()) {
                throw new IllegalStateException("`" + declared + "` is declared to take "
                        + declared.arity() + " arguments and this call stands with " + args.size());
            }
        }

        /** What the name was resolved to. Every rule about an operation is keyed by this. */
        public ValueName operation() {
            return declared.operation();
        }

        /**
         * What a reader that keeps no call standing says when one reaches it: this compiler failed to
         * expand it. Said here so every such reader says it the same way, and says it about the node
         * rather than about the operation — which of them a reader has bytecode for is not the
         * question.
         */
        public IllegalStateException unexpectedIn(String reader) {
            return new IllegalStateException(
                    "a preserved call (" + declared + ") reached " + reader + ", at " + pos);
        }
    }

    /**
     * Applying a function value the body holds: a helper's function parameter, or a lambda a
     * {@code let} bound that escaped.
     *
     * <p>Apart from {@link Call} because it is a different operation — one loads a value and invokes
     * it, the other names something declared elsewhere — and because only this one applies something
     * the body binds. Held together, which of the two a node was had to be worked out downstream by
     * looking the name up among the locals, and the binding was lost on the way.
     */
    record Apply(Read fn, List<Core> args, Type type, SourcePos pos) implements Core {}

    /**
     * {@code occurrence} is which fork of the model this is: the fork the source wrote it as,
     * carried from the AST so that the copies an expansion made of one fork are one coverage
     * obligation ({@link SourceConstructOrigin}), and the copy of the body it stands in — a call's,
     * a build's, or both nested — ({@link souther.compiler.types.OccurrenceLineage}).
     *
     * <p>{@code expansion} is what a copy is called where the rules a call supplied are looked up,
     * innermost first, empty where the fork stands in the body as written. What settles a fork can
     * be a rule the caller supplied, and which rule that was is recorded against the copy's bindings
     * — so it travels with the fork rather than being recovered from whatever names the fork's own
     * subtree happens to hold. A rewrite that keeps a fork keeps this.
     *
     * <p><b>Beside the occurrence and not folded into it.</b> The two say which copy in two
     * vocabularies, and each is the vocabulary its reader already speaks: what a construct is a copy
     * of is settled by the calls the source wrote, and what a binding belongs to is the inlining
     * pass's own answer, which is what the table of supplied rules is keyed by. Either derived from
     * the other would put one reader's counting inside the other's identity.
     */
    record If(Core cond, Core then, Core els, ForkPlace place, Type type, SourcePos pos)
            implements Core {

        public If {
            if (place == null) {
                throw new IllegalArgumentException("a fork stands somewhere: some fork of the"
                        + " model, in some copy of the body that wrote it");
            }
        }

        /** Which fork of the model this is, in whichever copy of the body it stands. */
        public ConstructOccurrence occurrence() {
            return place.occurrence();
        }

        /** What the copy is called where the rules a call supplied are looked up. */
        public List<souther.compiler.types.BindingOwner> expansion() {
            return place.expansion();
        }

        /** What the source wrote, as for {@link Binary}. */
        public SourceConstructOrigin origin() {
            return occurrence().origin();
        }
    }

    /**
     * An attempted construction: {@code construct}'s invariant decides the branch. It is built and
     * bound to {@code binder} in {@code then} when the invariant holds, and a departure in
     * {@code els} is taken when it does not. Emitted from the {@code __construct} the plain
     * construction already goes through — what differs is that the {@code Result} is branched on
     * rather than handed to {@code ConstraintViolation.orThrow}.
     *
     * <p>With one departure naming no clause, any failure takes it. With several, the failing clause
     * the {@code Result} carries selects one; the checker has already established that every named
     * clause is answered, so one always matches.
     *
     * <p>{@code occurrence} and {@code expansion} say which fork of the model this is and what its
     * copy is called where supplied rules are looked up, as they do for {@link If}.
     */
    record IfConstructed(Construct construct, Binder binder, Core then, List<ElseArm> els,
                         ForkPlace place, Type type, SourcePos pos) implements Core {

        public IfConstructed {
            if (place == null) {
                throw new IllegalArgumentException("a fork stands somewhere: some fork of the"
                        + " model, in some copy of the body that wrote it");
            }
        }

        /** Which fork of the model this is, in whichever copy of the body it stands. */
        public ConstructOccurrence occurrence() {
            return place.occurrence();
        }

        /** What the copy is called where the rules a call supplied are looked up. */
        public List<souther.compiler.types.BindingOwner> expansion() {
            return place.expansion();
        }

        /** What the source wrote, as for {@link Binary}. */
        public SourceConstructOrigin origin() {
            return occurrence().origin();
        }
    }

    /** One departure of an attempted construction: the clause it answers ({@link Optional#empty()}
     * for any failure) and the value taken. */
    record ElseArm(Optional<String> clause, Core body) {}

    /**
     * A local binding.
     *
     * <p>{@code bindType} is the type {@code binder} is in force at in {@code body}: the type the
     * checker entered it into the environment at. It is the checker's decision and is not
     * {@code value}'s type: the value may be one case of the sum the binding is read at — an
     * annotation wider than the value, or a declared sum parameter an expansion binds its argument
     * at.
     *
     * <p>{@code type} is the type of the whole expression, which an expansion may widen past its
     * body's.
     */
    record LetIn(Binder binder, Type bindType, Core value, Core body, Type type, SourcePos pos)
            implements Core {

        public String name() {
            return binder.name();
        }
    }

    /** A second-class block: a step passed to a recursive combinator, or an escaping lambda a {@code
     * let} binds (a closure). It has no value of its own: the call it is passed to emits its body
     * inline, and only a block that escapes into a first-class position becomes a class.
     *
     * <p>{@code paramTypes} are the types its body reads its parameters at, and are held because the
     * body cannot say them. What it answers is its body's type and is not held: a rewrite of the body
     * changes what the block answers with it. A type the function stands as at a position is not the
     * block's — that is a {@link Widen} around it.
     */
    record Block(List<Binder> params, List<Type> paramTypes, Core body, SourcePos pos)
            implements Core {

        public Block {
            params = List.copyOf(params);
            paramTypes = List.copyOf(paramTypes);
            if (params.size() != paramTypes.size()) {
                throw new IllegalArgumentException("a block of " + params.size()
                        + " parameters reads its body at " + paramTypes.size() + " types");
            }
        }

        @Override
        public Type.FnOf type() {
            return new Type.FnOf(paramTypes, body.type());
        }

        /** How the parameters were written, in order. */
        public List<String> paramNames() {
            return params.stream().map(Binder::name).toList();
        }
    }

    record ListLit(List<Core> elements, Type type, SourcePos pos) implements Core {}

    /** A value given to a {@code ?} field, wrapped (spec §algebraic-types). Construction of a data is the one
     * place an optional is made, so this node has no surface form: {@code Some(...)} is not a call
     * anyone can write, and the type it produces is never named (ADR-0011). */
    record OptionSome(Core value, Type type, SourcePos pos) implements Core {}

    /** {@code None} given to a {@code ?} field: the empty optional. */
    record OptionNone(Type type, SourcePos pos) implements Core {}

    /** A tuple {@code (e1, e2, ...)} (ADR-0036); the backend emits it as an {@code Object[]}. */
    record Tuple(List<Core> elements, Type type, SourcePos pos) implements Core {}

    /** Reads a tuple element by index (a {@code let (x, y) = t} destructure); {@code arity} is the
     * pattern's name count, checked against the tuple's size (ADR-0036). */
    record TupleGet(Core tuple, int index, int arity, Type type, SourcePos pos) implements Core {}

    /** What one field of a construction is given. {@code pos} is where the value was written, which
     * for a field a spread supplies is the spread. */
    record FieldValue(String field, Core value, SourcePos pos) {}

    /**
     * Making a value of a declared type — the one node a body creates a representation with. Every
     * way a source writes one is this: a record literal, a literal spreading another value's fields,
     * a newtype's constructor, and the arithmetic that re-wraps a newtype (spec §newtype-arithmetic).
     * What a construction builds is therefore settled once, where this is built, rather than worked
     * out again by each reader from the shape it was written in.
     *
     * <p>{@code values} is every declared field, in declaration order, and holds no spread: the
     * value a spread supplies is the read of that field off the spread source, resolved here. A
     * reader asking what this builds asks {@code values}, and the order it asks in is the order the
     * fields are evaluated.
     */
    record Construct(TypeSymbol.AtModule typeName, List<FieldValue> values, Type type,
                     SourcePos pos) implements Core {}

    /**
     * What an arm selects and what it binds, both decided by the checker.
     *
     * <p>{@code cases} are the cases the arm answers for, in the order they are written; more than
     * one is an or-pattern. {@code binding} is what the value is read as once the arm is taken, and
     * it is the arm's own rather than any one case's: an or-pattern binds the subject, because no
     * single case type fits all of its alternatives.
     *
     * <p><b>As the checker resolved them, and not as they were written.</b> A case is carried here
     * as a {@link ResolvedCase} — what the value is tested and read as, together with the atoms
     * selecting it covers. The second half is a fact about the declarations this compile read: a
     * case that is itself a sum stands for the leaves under it (spec §sum-data), so {@code OnceKind}
     * selects two of them where {@code Station} selects one. Kept as a selector alone it was
     * unrecoverable below this point — nothing downstream holds declarations to ask — and every
     * reader that needed which case of a subject an arm picked answered from the name, which says
     * neither how many leaves it reaches nor whether it is an optional's carrier.
     *
     * <p>Nothing here is worked out again downstream. A reader emitting this tests each case's
     * {@link Refinement} and reads the binding through {@code binding}, and never asks whether the
     * subject was an optional, whether the arm named one case or several, or whether a case is a
     * primitive. Those are the questions {@code Core} exists to have answered already.
     */
    sealed interface ResolvedPattern {

        /** The cases the arm answers for, as this compile resolved them, in the order they are
         *  written. */
        List<ResolvedCase> cases();

        /** The same, as what tests and reads a value — which is what a backend emits. A projection
         *  of {@link #cases()} and answered as one: what an arm selects is that value's to say. */
        default List<CaseSelector> selectors() {
            return cases().stream().map(ResolvedCase::selector).toList();
        }

        /**
         * The one case this arm selects, or empty where it selects no one case.
         *
         * <p>Asked here rather than worked out from the shape of the pattern. A reader that decided
         * from the pattern's shape that one case must be there, and then took its name, would be
         * rebuilding a decision this already holds out of less than it was made from. That is how
         * an optional's {@code Some} came to be read as a sum's case named {@code Some}.
         *
         * <p>Empty is an answer and not an absence of one: an or-pattern selects several cases and
         * therefore no one of them, which is a fact about what was written and not a count standing
         * in for one. What that selection then comes to at a position — one of the distinctions the
         * declarations state there, or none — is the other question, and it is answered from the
         * atoms this carries rather than from anything about the pattern.
         */
        Optional<ResolvedCase> selectedCase();

        /**
         * What the value is read as once the arm is taken.
         *
         * <p>Derived rather than carried. What an arm binds follows from what it selects — one case
         * binds what that case's carrier holds, several bind the subject — so holding the two apart
         * would be holding one fact in two places, and a pattern selecting an optional's absent
         * carrier while binding its present one would be a Core the emitter has no meaning for: it
         * would test one carrier and read the value out of the other.
         */
        Refinement binding();

        /** The cases this answers for. */
        default List<TypeSymbol> caseTypes() {
            List<TypeSymbol> out = new java.util.ArrayList<>();
            for (CaseSelector selector : selectors()) {
                out.add(selector.name());
            }
            return out;
        }

        /** The type the binding takes inside the arm, or null where the arm binds nothing readable. */
        default Type bindType() {
            return binding().bound();
        }

        /** An arm answering for one case, which binds what that case's carrier holds. */
        record Single(ResolvedCase selected) implements ResolvedPattern {

            public Single {
                if (selected == null) {
                    throw new IllegalArgumentException("an arm selects a case");
                }
            }

            @Override
            public List<ResolvedCase> cases() {
                return List.of(selected);
            }

            @Override
            public Optional<ResolvedCase> selectedCase() {
                return Optional.of(selected);
            }

            @Override
            public Refinement binding() {
                return selected.refinement();
            }
        }

        /**
         * An arm answering for several, which binds the subject: no one case type fits all of its
         * alternatives, and every alternative is already the subject.
         */
        record AnyOf(List<ResolvedCase> cases, Type subject) implements ResolvedPattern {

            public AnyOf {
                if (cases == null || cases.size() < 2) {
                    throw new IllegalArgumentException("an arm answering for several names several");
                }
                if (subject == null) {
                    throw new IllegalArgumentException("what such an arm binds is the subject");
                }
                cases = List.copyOf(cases);
            }

            @Override
            public Optional<ResolvedCase> selectedCase() {
                return Optional.empty();
            }

            @Override
            public Refinement binding() {
                return new Refinement.Direct(subject);
            }
        }
    }

    /** One arm of a {@code match}: what it selects, what it calls the value, and what it answers. */
    record Case(ResolvedPattern pattern, Binder binder, Core body, SourcePos pos) {

        /** How the binding was written, or null where the arm binds nothing. */
        public String bindingName() {
            return binder == null ? null : binder.name();
        }

        /** The cases this arm answers for. */
        public List<TypeSymbol> caseTypes() {
            return pattern.caseTypes();
        }

        /**
         * The type the value this arm binds is cast to when it is bound, or null where binding it
         * casts nothing: the arm binds nothing, or what it binds is the subject as it already stands.
         *
         * <p>The one answer, read by the emitter and by whatever asks which classes an emitted
         * {@code match} names, so that they do not come to disagree about which arms cast.
         *
         * @param subject the type of the value the {@code match} is over
         */
        public Type castOnBinding(Type subject) {
            if (binder == null) {
                return null;
            }
            return switch (pattern.binding()) {
                // What an optional holds is opened and cast to the type it was checked to hold.
                case Refinement.OptionPresent wrapped -> wrapped.bound();
                // A case is cast to its own type, unless nothing narrowed it: then it is the subject.
                case Refinement.Direct itself ->
                        itself.bound() == null || itself.bound().equals(subject) ? null : itself.bound();
                case Refinement.OptionAbsent _ -> null;
            };
        }

        /** The one case this arm selects, as this compile resolved it, or empty where it selects no
         *  one case. */
        public Optional<ResolvedCase> selectedCase() {
            return pattern.selectedCase();
        }

        /** The type the binding takes inside this arm. */
        public Type bindType() {
            return pattern.bindType();
        }

        /** The same arm answering a rewritten body — what a pass rewriting expressions produces, so
         * a rewrite carries what the arm selects and binds rather than restating it. */
        public Case answering(Core rewritten) {
            return rewritten == body ? this : new Case(pattern, binder, rewritten, pos);
        }
    }

    /**
     * {@code occurrence} and {@code expansion} say which fork of the model this is and what its copy
     * is called where supplied rules are looked up, as they do for {@link If}.
     */
    record Match(Core scrutinee, List<Case> cases, ForkPlace place, Type type, SourcePos pos)
            implements Core {

        public Match {
            if (place == null) {
                throw new IllegalArgumentException("a fork stands somewhere: some fork of the"
                        + " model, in some copy of the body that wrote it");
            }
        }

        /** Which fork of the model this is, in whichever copy of the body it stands. */
        public ConstructOccurrence occurrence() {
            return place.occurrence();
        }

        /** What the copy is called where the rules a call supplied are looked up. */
        public List<souther.compiler.types.BindingOwner> expansion() {
            return place.expansion();
        }

        /** What the source wrote, as for {@link Binary}. */
        public SourceConstructOrigin origin() {
            return occurrence().origin();
        }
    }

    /**
     * A value standing as a type other than its own, where the checker decided that it may.
     *
     * <p>{@code value} is what is evaluated, at the type it was worked out at; {@code type} is what
     * the position it stands in takes it as. A branch answering one case of the sum its {@code if}
     * joins at, an argument handed to a wider parameter, a list of a case given where a list of the
     * sum is asked for, a function taking a sum given where one taking a case of it is asked for:
     * each is this, the same way, with nothing about why the checker let it stand there. That is the
     * checker's to answer, and a reader of this reads that it did rather than answering again.
     *
     * <p>Only where the two differ. A value standing as its own type is in its position as it is, and
     * a node saying so would say nothing. So a slot the checker placed a value in at a type holds
     * something of that type: the value itself where the two are equal, and this where they are not.
     *
     * <p>No operation. Whether standing as a wider type costs anything at run time is a question about
     * how a backend lays the two types out, and not one this answers. A reader asking what a body
     * does, rather than what it was checked to be, reads through it with {@link #withoutStanding}.
     *
     * <p>It has no place of its own: nothing was written for it.
     */
    record Widen(Core value, Type type) implements Core {

        public Widen {
            if (value == null || type == null) {
                throw new IllegalArgumentException("a value stands as some type");
            }
            if (value.type().equals(type)) {
                throw new IllegalArgumentException(
                        "a value standing as its own type is not widened: " + type);
            }
            if (value instanceof Widen) {
                throw new IllegalArgumentException(
                        "a value stands at one position once, as what that position takes it as: "
                                + value.type() + " as " + type);
            }
        }

        @Override
        public SourcePos pos() {
            return value.pos();
        }
    }

    /**
     * {@code e} as what it evaluates, with the type it stands as at its position set aside: the value
     * a {@link Widen} holds, and {@code e} itself where nothing widened it.
     *
     * <p>What a reader asking which expression is here asks through: whether it is a read, a call, a
     * construction. Standing as a wider type changes none of that.
     */
    static Core withoutStanding(Core e) {
        return e instanceof Widen w ? w.value() : e;
    }

    /**
     * {@code value} standing as {@code type}: {@code value} itself where it already is of that type,
     * and a {@link Widen} of it where it is not.
     *
     * <p>A {@code value} already standing as {@code type} is that value, the same node. One that is a
     * {@link Widen} of something else is set aside first, so that a value restated at a new position
     * stands there as what that position takes it as, once.
     */
    static Core standingAs(Core value, Type type) {
        if (value.type().equals(type)) {
            return value;
        }
        Core bare = withoutStanding(value);
        return bare.type().equals(type) ? bare : new Widen(bare, type);
    }

    /** {@code unreachable "reason"}: the position it stands in gets no value, and the reason is the
     * message the abort carries. Its type is {@link Type.Never}, which fits whatever was expected. */
    record Unreachable(String reason, Type type, SourcePos pos) implements Core {

        /**
         * The shape this leaves on the stack where its position asks for {@code expected}: what the
         * position asked for, or — where it asked for nothing — its own type, which is {@link
         * Type.Never} and is refused rather than emitted.
         */
        public Type shapeAt(Type expected) {
            return expected != null ? expected : type;
        }
    }

    /**
     * The type the branches of {@code e} leave on the stack: what the position asked for, or — where
     * it asked for nothing — the one the checker joined the branches at. A branch that answers
     * {@code unreachable} has no type of its own to merge with the others, so it takes this one.
     *
     * <p>The one answer, read by the emitter and by whatever asks which classes an emitted branch
     * names: the shape is what a value is cast to, so written out in each the two would agree only
     * until one of them moved.
     */
    static Type shapeOf(Core e, Type expected) {
        return expected != null ? expected : e.type();
    }

    /**
     * {@code e} with each of its slots replaced by what the operator for that slot answers, the
     * node's own kind, position and the types it holds kept — or {@code e} itself where every slot
     * answered what it was given, so a walk that only reads allocates nothing. A {@link Block} holds
     * no type for what it answers, so what it answers follows its rewritten body.
     *
     * <p>The children of a node occupy three kinds of slot, which differ in what may stand there.
     *
     * <ul>
     *   <li>An expression slot takes any Core expression.</li>
     *   <li>A name slot takes only a {@link Read}: an applied function is a binding holding one, and
     *       the backend loads that binding's slot, so an expression there would have nothing to be
     *       loaded from.</li>
     *   <li>A construction slot takes only a {@link Construct}: an attempt tests whether a
     *       construction holds, and there is no other kind of expression whose invariant could
     *       fail.</li>
     * </ul>
     *
     * <p>This is the one place that says which slots a node has, and both {@link #mapChildren} and
     * {@link #forEachChild} are derived from it. Exhaustive over {@code Core}: a node kind added
     * later stops the build here.
     */
    private static Core atSlots(Core e, java.util.function.UnaryOperator<Core> atExpr,
                                java.util.function.UnaryOperator<Read> atName,
                                java.util.function.UnaryOperator<Construct> atConstruction) {
        return switch (e) {
            case Int x -> x;
            case Decimal x -> x;
            case Str x -> x;
            case Bool x -> x;
            case Temporal x -> x;
            case Read x -> x;
            case UnitValue x -> x;
            case MaterialisedValue x -> x;
            case OptionNone x -> x;
            case Unreachable x -> x;
            // What it holds is rewritten like any other value; the type it stands as is kept, and a
            // rewrite that brings the value to that type leaves nothing to widen.
            case Widen w -> {
                Core value = atExpr.apply(w.value());
                yield value == w.value() ? w : standingAs(value, w.type());
            }
            case Neg n -> {
                Core operand = atExpr.apply(n.operand());
                yield operand == n.operand() ? n : new Neg(operand, n.type(), n.pos());
            }
            case FieldAccess fa -> {
                Core target = atExpr.apply(fa.target());
                yield target == fa.target() ? fa
                        : new FieldAccess(target, fa.field(), fa.type(), fa.pos());
            }
            case Binary b -> {
                Core left = atExpr.apply(b.left());
                Core right = atExpr.apply(b.right());
                yield left == b.left() && right == b.right() ? b
                        : new Binary(b.op(), left, right, b.reading(), b.occurrence(), b.type(),
                                b.pos());
            }
            case Call c -> {
                List<Core> args = each(c.args(), atExpr);
                yield args == c.args() ? c
                        : new Call(c.fn(), args, c.occurrence(), c.settlement(), c.type(), c.pos());
            }
            // Its arguments are children like any other, so a pass that asks what a body reads
            // reaches them without knowing what was kept standing over them.
            case PreservedCall p -> {
                List<Core> args = each(p.args(), atExpr);
                yield args == p.args() ? p
                        : new PreservedCall(p.declared(), args, p.place(), p.type(), p.pos());
            }
            // what is applied is a binding holding a function, which the backend loads: a name slot
            case Apply a -> {
                Read fn = atName.apply(a.fn());
                List<Core> args = each(a.args(), atExpr);
                yield fn == a.fn() && args == a.args() ? a
                        : new Apply(fn, args, a.type(), a.pos());
            }
            case If iff -> {
                Core cond = atExpr.apply(iff.cond());
                Core then = atExpr.apply(iff.then());
                Core els = atExpr.apply(iff.els());
                yield cond == iff.cond() && then == iff.then() && els == iff.els() ? iff
                        : new If(cond, then, els, iff.place(), iff.type(), iff.pos());
            }
            case IfConstructed ic -> {
                Construct construct = atConstruction.apply(ic.construct());
                Core then = atExpr.apply(ic.then());
                List<ElseArm> els = each(ic.els(), arm -> {
                    Core body = atExpr.apply(arm.body());
                    return body == arm.body() ? arm : new ElseArm(arm.clause(), body);
                });
                yield construct == ic.construct() && then == ic.then() && els == ic.els() ? ic
                        : new IfConstructed(construct, ic.binder(), then, els, ic.place(),
                                ic.type(), ic.pos());
            }
            case LetIn li -> {
                Core value = atExpr.apply(li.value());
                Core body = atExpr.apply(li.body());
                yield value == li.value() && body == li.body() ? li
                        : new LetIn(li.binder(), li.bindType(), value, body, li.type(), li.pos());
            }
            case Block b -> {
                Core body = atExpr.apply(b.body());
                yield body == b.body() ? b : new Block(b.params(), b.paramTypes(), body, b.pos());
            }
            case ListLit lit -> {
                List<Core> elements = each(lit.elements(), atExpr);
                yield elements == lit.elements() ? lit
                        : new ListLit(elements, lit.type(), lit.pos());
            }
            case OptionSome s -> {
                Core value = atExpr.apply(s.value());
                yield value == s.value() ? s : new OptionSome(value, s.type(), s.pos());
            }
            case Tuple t -> {
                List<Core> elements = each(t.elements(), atExpr);
                yield elements == t.elements() ? t : new Tuple(elements, t.type(), t.pos());
            }
            case TupleGet tg -> {
                Core tuple = atExpr.apply(tg.tuple());
                yield tuple == tg.tuple() ? tg
                        : new TupleGet(tuple, tg.index(), tg.arity(), tg.type(), tg.pos());
            }
            case Construct nd -> atSlots(nd, atExpr);
            case Match m -> {
                Core scrutinee = atExpr.apply(m.scrutinee());
                List<Case> cases = each(m.cases(), c -> c.answering(atExpr.apply(c.body())));
                yield scrutinee == m.scrutinee() && cases == m.cases() ? m
                        : new Match(scrutinee, cases, m.place(), m.type(), m.pos());
            }
        };
    }

    /**
     * The same for a construction, whose type is kept: it has an expression slot per declared field
     * and no others. What a spread supplied is one of those slots, resolved before this is built, so
     * a pass rewrites it as it rewrites any other value a field is given.
     *
     * <p>Said once and read twice — by the walk above, where a construction is an expression like any
     * other, and by the overload of {@code mapChildren} that takes a construction, which is how a
     * pass recurses through the one an attempt holds.
     */
    private static Construct atSlots(Construct nd, java.util.function.UnaryOperator<Core> atExpr) {
        List<FieldValue> values = each(nd.values(), v -> {
            Core value = atExpr.apply(v.value());
            return value == v.value() ? v : new FieldValue(v.field(), value, v.pos());
        });
        return values == nd.values() ? nd
                : new Construct(nd.typeName(), values, nd.type(), nd.pos());
    }

    /** {@code xs} with {@code f} applied to each, or {@code xs} itself where none of them changed. */
    private static <T> List<T> each(List<T> xs, java.util.function.UnaryOperator<T> f) {
        List<T> out = null;
        for (int i = 0; i < xs.size(); i++) {
            T before = xs.get(i);
            T after = f.apply(before);
            if (out == null && after != before) {
                out = new java.util.ArrayList<>(xs.subList(0, i));
            }
            if (out != null) {
                out.add(after);
            }
        }
        return out == null ? xs : out;
    }

    /**
     * {@code e} with each of its slots replaced by what the operator for that slot answers, the
     * node's own kind, position and the types it holds kept, as {@link #atSlots} says. A Core-to-Core
     * pass recurses through this rather than hand-copying every node kind.
     *
     * <p>An operator per slot kind, so a rewrite cannot put an expression where the backend can only
     * load a binding, or something other than a construction where an attempt tests one.
     *
     * <p>A node that carries a fact the checker settled about it — a {@link Call}'s
     * {@link CallSettlement} — keeps that fact across the rewrite this makes, which is right where
     * the rewrite preserves what the node means and stale where it does not: a pass that changes what
     * a slot evaluates to a different meaning owes that fact a rebuild of its own, not a rewrite that
     * carries the old one forward unasked.
     */
    static Core mapChildren(Core e, java.util.function.UnaryOperator<Core> onExprSlot,
                            java.util.function.UnaryOperator<Read> onNameSlot,
                            java.util.function.UnaryOperator<Construct> onConstructionSlot) {
        return atSlots(e, onExprSlot, onNameSlot, onConstructionSlot);
    }

    /**
     * The same, recursing into a construction slot with the operators the other slots are given —
     * what a pass that rewrites expressions wants, since a construction an attempt holds is as much
     * an expression as anything else and no such pass has anything else to say about one.
     */
    static Core mapAll(Core e, java.util.function.UnaryOperator<Core> onExprSlot,
                       java.util.function.UnaryOperator<Read> onNameSlot) {
        return atSlots(e, onExprSlot, onNameSlot, nd -> atSlots(nd, onExprSlot));
    }

    /**
     * The same over a construction, answering one — what a recursive pass does at a construction
     * slot.
     *
     * <p>A construction slot is not a leaf the way a name slot is, so a pass that recurses has to say
     * how it recurses into one. Handing it back unchanged stops the pass at an attempt, which no pass
     * means: what an attempt tries to build is as much part of the body as anything else. It takes
     * only the expression operator, a construction having none of the other slot kinds.
     */
    static Construct mapChildren(Construct nd, java.util.function.UnaryOperator<Core> onExprSlot) {
        return atSlots(nd, onExprSlot);
    }

    /**
     * Applies {@code f} to each direct child of {@code e} — the read-only counterpart of
     * {@link #mapChildren}. Every slot is a child whatever kind it is, so a pass that asks what a
     * body reads reaches the binding an application invokes, and the construction an attempt tests,
     * without knowing that either position exists.
     */
    static void forEachChild(Core e, java.util.function.Consumer<Core> f) {
        atSlots(e, child -> {
            f.accept(child);
            return child;
        }, child -> {
            f.accept(child);
            return child;
        }, child -> {
            f.accept(child);
            return child;
        });
    }

}
