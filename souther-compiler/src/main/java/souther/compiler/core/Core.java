package souther.compiler.core;

import souther.compiler.types.BindingId;
import souther.compiler.types.CaseSelector;
import souther.compiler.types.CoverageOrigin;
import souther.compiler.types.Refinement;
import souther.compiler.types.ReachName;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;
import souther.compiler.diag.SourcePos;
import souther.compiler.ast.Hir;

import java.math.BigDecimal;
import java.util.List;
import java.util.Optional;

/**
 * The Core IR (ADR-0021): the lowered form of a behavior body the backend emits from.
 *
 * <p>Core is the surface expression AST after the {@link souther.compiler.check.Lower}
 * stage has inlined helpers and desugared surface-only forms. It differs from the AST in what it
 * makes explicit: a construct the backend used to re-detect and shape during emission becomes its
 * own node here, so the backend only emits.
 *
 * <p>Every node carries {@link #type()}: the type the checker decided for it (issue #81). The
 * checker is the only producer of Core — it builds the tree as it types a body
 * ({@code Elaborator.elaborate}) — so the backend reads those decisions instead of inferring the
 * same types a second time.
 *
 * <p>A name in a body is one of two nodes, not one: a read of something the body binds, and a unit
 * data written as its own value. They were one, and the emitter told them apart by looking the
 * spelling up in its slots and falling back when it found nothing — which is an answer about a
 * name, decided by its text.
 *
 * <p>A surface-only node (a list comprehension) never appears — the Lower stage has already
 * rewritten it.
 */
public sealed interface Core {

    SourcePos pos();

    /** The type the checker decided for this expression. */
    Type type();

    record Int(long value, Type type, SourcePos pos) implements Core {}

    record Decimal(BigDecimal value, Type type, SourcePos pos) implements Core {}

    record Str(String value, Type type, SourcePos pos) implements Core {}

    record Bool(boolean value, Type type, SourcePos pos) implements Core {}

    /** A read of something the body binds: a parameter, a {@code let}, a lambda's parameter, a
     * {@code match} arm's binding. {@code binding} is which one; {@code name} is what to call the
     * local it is emitted as, and what a diagnostic quotes. */
    record Read(String name, BindingId binding, Type type, SourcePos pos) implements Core {}

    /** A unit data written where a value goes: the type has one value, and naming it is that value
     * (spec §unit-data). Which unit is on the node, so nothing resolves a spelling again. */
    record UnitValue(TypeSymbol data, Type type, SourcePos pos) implements Core {}

    record Neg(Core operand, Type type, SourcePos pos) implements Core {}

    record FieldAccess(Core target, String field, Type type, SourcePos pos) implements Core {}

    /** {@code origin} is where the comparison was written; see {@link Hir.Binary}. */
    record Binary(Hir.BinOp op, Core left, Core right, CoverageOrigin origin, Type type,
                  SourcePos pos) implements Core {}

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
     * A callee some module named: the name that module reaches it by, and what that name was
     * resolved to.
     *
     * <p>Both, because they answer different questions and neither is derived from the other. The
     * backend emits the method the reach name spells; a reader asking what kind of thing was called —
     * a module's own helper, one of the language's operations, a behavior whose implementation comes
     * from outside — asks what the name denotes. Working the second out of the first would be
     * resolving a name this compiler resolved already, and a bare spelling reaches a helper and an
     * injected behavior alike.
     */
    record Reached(ReachName name, ValueName denotes) implements CallTarget {

        @Override
        public String rendered() {
            return name.rendered();
        }

        @Override
        public String toString() {
            return rendered();
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
     * A call to a builtin, an injected behavior, an intrinsic, or a recursive helper emitted as a
     * method — none of them bound by this body. A non-recursive helper is already inlined.
     *
     * <p>{@code fn} says what is applied ({@link CallTarget}). Where that is a name, it is the one
     * the module being emitted reaches the callee by, carried from where resolution settled it, and
     * held as what it is rather than as the spelling of it: the backend needs both the whole name, to
     * emit the method it calls, and the operation inside it, to reach the runtime method a library
     * call becomes — and taking the second out of the first meant splitting a name this compiler had
     * joined a moment earlier.
     */
    record Call(CallTarget fn, List<Core> args, Type type, SourcePos pos) implements Core {

        /** A call to a name, as the name it reaches and what that name denotes. */
        public Call(ReachName fn, ValueName denotes, List<Core> args, Type type, SourcePos pos) {
            this(new Reached(fn, denotes), args, type, pos);
        }

        /** The callee as it renders — the reach name for a call to one, the operation's own
         * spelling for one this compiler emits. What a method name is built from and what a report
         * quotes; never what a source wrote. */
        public String name() {
            return fn.rendered();
        }
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
     * <p>{@code operation} is what the name was resolved to, not how it was written: two spellings
     * that reach one operation are one of these, and having a type in common is not being the same
     * operation. A reader with no rule for what this names types it and learns nothing from it,
     * which is the difference between a representation keeping a call and an analysis understanding
     * one.
     */
    record PreservedCall(ValueName operation, List<Core> args, Type type,
                         SourcePos pos) implements Core {

        /**
         * What a reader that keeps no call standing says when one reaches it: this compiler failed to
         * expand it. Said here so every such reader says it the same way, and says it about the node
         * rather than about the operation — which of them a reader has bytecode for is not the
         * question.
         */
        public IllegalStateException unexpectedIn(String reader) {
            return new IllegalStateException(
                    "a preserved call (" + operation + ") reached " + reader + ", at " + pos);
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

    /** {@code origin} is the fork the source wrote this as, carried from the AST so that the copies
     * an expansion made of one fork are one coverage obligation ({@link CoverageOrigin}). */
    record If(Core cond, Core then, Core els, CoverageOrigin origin, Type type, SourcePos pos)
            implements Core {}

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
     */
    record IfConstructed(Construct construct, Hir.Binder binder, Core then, List<ElseArm> els,
                         CoverageOrigin origin, Type type, SourcePos pos) implements Core {}

    /** One departure of an attempted construction: the clause it answers ({@link Optional#empty()}
     * for any failure) and the value taken. */
    record ElseArm(Optional<String> clause, Core body) {}

    /** A local binding. What the source wrote as its type — {@code let x: T = e} — is already in
     * {@code value}'s type: the checker pushed the annotation into the value when it typed it, so an
     * empty collection bound here materialises at the written type rather than a bottom (issue #71). */
    record LetIn(Hir.Binder binder, Core value, Core body, Type type, SourcePos pos) implements Core {

        public String name() {
            return binder.name();
        }
    }

    /** A second-class block: a step passed to a recursive combinator, or an escaping lambda a {@code
     * let} binds (a closure). It has no value of its own: the call it is passed to emits its body
     * inline, and only a block that escapes into a first-class position becomes a class. Its {@code
     * type} is the {@link Type.FnOf} the checker gave it — the parameter types the context fixed, and
     * the body's result type. */
    record Block(List<Hir.Binder> params, Core body, Type type, SourcePos pos) implements Core {

        /** How the parameters were written, in order. */
        public List<String> paramNames() {
            return params.stream().map(Hir.Binder::name).toList();
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
    record Construct(TypeSymbol typeName, List<FieldValue> values, Type type,
                     SourcePos pos) implements Core {}

    /**
     * What an arm selects and what it binds, both decided by the checker.
     *
     * <p>{@code selectors} are the cases the arm answers for, in the order they are written; more
     * than one is an or-pattern. {@code binding} is what the value is read as once the arm is taken,
     * and it is the arm's own rather than any one selector's: an or-pattern binds the subject,
     * because no single case type fits all of its alternatives.
     *
     * <p>Nothing here is worked out again downstream. A reader emitting this tests each selector's
     * {@link Refinement} and reads the binding through {@code binding}, and never asks whether the
     * subject was an optional, whether the arm named one case or several, or whether a case is a
     * primitive. Those are the questions {@code Core} exists to have answered already.
     */
    record ResolvedPattern(List<CaseSelector> selectors, Refinement binding) {

        public ResolvedPattern {
            if (selectors == null || selectors.isEmpty()) {
                throw new IllegalArgumentException("an arm selects at least one case");
            }
            selectors = List.copyOf(selectors);
        }

        /** The cases this answers for. */
        public List<TypeSymbol> caseTypes() {
            List<TypeSymbol> out = new java.util.ArrayList<>();
            for (CaseSelector selector : selectors) {
                out.add(selector.name());
            }
            return out;
        }

        /** The type the binding takes inside the arm, or null where the arm binds nothing readable. */
        public Type bindType() {
            return binding == null ? null : binding.bound();
        }
    }

    /** One arm of a {@code match}: what it selects, what it calls the value, and what it answers. */
    record Case(ResolvedPattern pattern, Hir.Binder binding, Core body, SourcePos pos) {

        /** How the binding was written, or null where the arm binds nothing. */
        public String bindingName() {
            return binding == null ? null : binding.name();
        }

        /** The cases this arm answers for. */
        public List<TypeSymbol> caseTypes() {
            return pattern.caseTypes();
        }

        /** The type the binding takes inside this arm. */
        public Type bindType() {
            return pattern.bindType();
        }

        /** The same arm answering a rewritten body — what a pass rewriting expressions produces, so
         * a rewrite carries what the arm selects and binds rather than restating it. */
        public Case answering(Core rewritten) {
            return rewritten == body ? this : new Case(pattern, binding, rewritten, pos);
        }
    }

    record Match(Core scrutinee, List<Case> cases, CoverageOrigin origin, Type type, SourcePos pos)
            implements Core {}

    /** {@code unreachable "reason"}: the position it stands in gets no value, and the reason is the
     * message the abort carries. Its type is {@link Type.Never}, which fits whatever was expected. */
    record Unreachable(String reason, Type type, SourcePos pos) implements Core {}

    /**
     * {@code e} with each of its slots replaced by what the operator for that slot answers, the
     * node's own kind, type and position kept — or {@code e} itself where every slot answered what it
     * was given, so a walk that only reads allocates nothing.
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
            case Read x -> x;
            case UnitValue x -> x;
            case OptionNone x -> x;
            case Unreachable x -> x;
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
                        : new Binary(b.op(), left, right, b.origin(), b.type(), b.pos());
            }
            case Call c -> {
                List<Core> args = each(c.args(), atExpr);
                yield args == c.args() ? c : new Call(c.fn(), args, c.type(), c.pos());
            }
            // Its arguments are children like any other, so a pass that asks what a body reads
            // reaches them without knowing what was kept standing over them.
            case PreservedCall p -> {
                List<Core> args = each(p.args(), atExpr);
                yield args == p.args() ? p
                        : new PreservedCall(p.operation(), args, p.type(), p.pos());
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
                        : new If(cond, then, els, iff.origin(), iff.type(), iff.pos());
            }
            case IfConstructed ic -> {
                Construct construct = atConstruction.apply(ic.construct());
                Core then = atExpr.apply(ic.then());
                List<ElseArm> els = each(ic.els(), arm -> {
                    Core body = atExpr.apply(arm.body());
                    return body == arm.body() ? arm : new ElseArm(arm.clause(), body);
                });
                yield construct == ic.construct() && then == ic.then() && els == ic.els() ? ic
                        : new IfConstructed(construct, ic.binder(), then, els, ic.origin(), ic.type(),
                                ic.pos());
            }
            case LetIn li -> {
                Core value = atExpr.apply(li.value());
                Core body = atExpr.apply(li.body());
                yield value == li.value() && body == li.body() ? li
                        : new LetIn(li.binder(), value, body, li.type(), li.pos());
            }
            case Block b -> {
                Core body = atExpr.apply(b.body());
                yield body == b.body() ? b : new Block(b.params(), body, b.type(), b.pos());
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
                        : new Match(scrutinee, cases, m.origin(), m.type(), m.pos());
            }
        };
    }

    /**
     * The same for a construction, whose type is kept: it has an expression slot per declared field
     * and no others. What a spread supplied is one of those slots, resolved before this is built, so
     * a pass rewrites it as it rewrites any other value a field is given.
     *
     * <p>Said once and read twice — by the walk above, where a construction is an expression like any
     * other, and by {@link #mapChildren(Construct, java.util.function.UnaryOperator,
     * java.util.function.UnaryOperator)}, which is how a pass recurses through the one an attempt
     * holds.
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
     * node's own kind, type and position kept. A Core-to-Core pass recurses through this rather than
     * hand-copying every node kind.
     *
     * <p>An operator per slot kind, so a rewrite cannot put an expression where the backend can only
     * load a binding, or something other than a construction where an attempt tests one.
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
