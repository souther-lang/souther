package souther.compiler.core;

import souther.compiler.types.BindingId;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;
import souther.compiler.diag.SourcePos;
import souther.compiler.ast.Ast;

import java.math.BigDecimal;
import java.util.List;
import java.util.Optional;

/**
 * The Core IR (ADR-0021): the lowered form of a behavior body the backend emits from.
 *
 * <p>Core is the surface expression AST after the {@link souther.compiler.check.Lower}
 * stage has inlined helpers and desugared surface-only forms. It differs from the AST in what it
 * makes explicit: a construct the backend used to re-detect and shape during emission becomes its
 * own node here, so the backend only emits. Later slices add explicit nodes for {@code match}
 * lowering and closure conversion, and drop the corresponding special cases from the emitter.
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
    record UnitValue(TypeName data, Type type, SourcePos pos) implements Core {}

    record Neg(Core operand, Type type, SourcePos pos) implements Core {}

    record FieldAccess(Core target, String field, Type type, SourcePos pos) implements Core {}

    record Binary(Ast.BinOp op, Core left, Core right, Type type, SourcePos pos) implements Core {}

    /** A call to a builtin, an injected behavior, an intrinsic, or a recursive helper emitted as a
     * method — each reached by the name it is declared under, none of them bound by this body. A
     * non-recursive helper is already inlined. */
    record Call(String fn, List<Core> args, Type type, SourcePos pos) implements Core {}

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

    record If(Core cond, Core then, Core els, Type type, SourcePos pos) implements Core {}

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
    record IfConstructed(NewData construct, Ast.Binder binder, Core then, List<ElseArm> els,
                         Type type, SourcePos pos) implements Core {}

    /** One departure of an attempted construction: the clause it answers ({@link Optional#empty()}
     * for any failure) and the value taken. */
    record ElseArm(Optional<String> clause, Core body) {}

    /** A local binding. What the source wrote as its type — {@code let x: T = e} — is already in
     * {@code value}'s type: the checker pushed the annotation into the value when it typed it, so an
     * empty collection bound here materialises at the written type rather than a bottom (issue #71). */
    record LetIn(Ast.Binder binder, Core value, Core body, Type type, SourcePos pos) implements Core {

        public String name() {
            return binder.name();
        }
    }

    /** A second-class block: a step passed to a recursive combinator, or an escaping lambda a {@code
     * let} binds (a closure). Kept as its own node until closure conversion gets an explicit Core form.
     * Its {@code type} is the {@link Type.FnOf} the checker gave it — the parameter types the context
     * fixed, and the body's result type. */
    record Block(List<Ast.Binder> params, Core body, Type type, SourcePos pos) implements Core {

        /** How the parameters were written, in order. */
        public List<String> paramNames() {
            return params.stream().map(Ast.Binder::name).toList();
        }
    }

    record ListLit(List<Core> elements, Type type, SourcePos pos) implements Core {}

    /** A value given to a {@code ?} field, wrapped (spec 7.3). Construction of a data is the one
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

    record FieldInit(String name, Core value, SourcePos pos) {}

    /** {@code spreads} are the bindings the construction copies fields from — reads, not binders:
     * a spread names a value in force, it does not introduce one. */
    record NewData(TypeName typeName, List<FieldInit> inits, List<Read> spreads, Type type,
                   SourcePos pos) implements Core {

        /** How each spread source was written, in order. */
        public List<String> spreadNames() {
            return spreads.stream().map(Read::name).toList();
        }
    }

    /** {@code bindType} is the type the case binding takes inside the arm — the case type a union
     * narrows to, or the element a {@code Some x} opens. */
    record Case(List<TypeName> caseTypes, Ast.Binder binding, Core body, Type bindType,
                SourcePos pos) {

        /** How the binding was written, or null where the arm binds nothing. */
        public String bindingName() {
            return binding == null ? null : binding.name();
        }
    }

    record Match(Core scrutinee, List<Case> cases, Type type, SourcePos pos) implements Core {}

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
     *   <li>A name slot takes only a {@link Read}: a construction's spread copies the fields of a
     *       binding and an applied function is a binding holding one, and the backend loads that
     *       binding's slot, so an expression there would have nothing to be loaded from.</li>
     *   <li>A construction slot takes only a {@link NewData}: an attempt tests whether a construction
     *       holds, and there is no other kind of expression whose invariant could fail.</li>
     * </ul>
     *
     * <p>This is the one place that says which slots a node has, and both {@link #mapChildren} and
     * {@link #forEachChild} are derived from it. Exhaustive over {@code Core}: a node kind added
     * later stops the build here.
     */
    private static Core atSlots(Core e, java.util.function.UnaryOperator<Core> atExpr,
                                java.util.function.UnaryOperator<Read> atName,
                                java.util.function.UnaryOperator<NewData> atConstruction) {
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
                        : new Binary(b.op(), left, right, b.type(), b.pos());
            }
            case Call c -> {
                List<Core> args = each(c.args(), atExpr);
                yield args == c.args() ? c : new Call(c.fn(), args, c.type(), c.pos());
            }
            // what is applied is a binding holding a function: a name slot, the same kind a spread is
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
                        : new If(cond, then, els, iff.type(), iff.pos());
            }
            case IfConstructed ic -> {
                NewData construct = atConstruction.apply(ic.construct());
                Core then = atExpr.apply(ic.then());
                List<ElseArm> els = each(ic.els(), arm -> {
                    Core body = atExpr.apply(arm.body());
                    return body == arm.body() ? arm : new ElseArm(arm.clause(), body);
                });
                yield construct == ic.construct() && then == ic.then() && els == ic.els() ? ic
                        : new IfConstructed(construct, ic.binder(), then, els, ic.type(), ic.pos());
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
            case NewData nd -> {
                List<Read> spreads = each(nd.spreads(), atName);
                List<FieldInit> inits = each(nd.inits(), i -> {
                    Core value = atExpr.apply(i.value());
                    return value == i.value() ? i : new FieldInit(i.name(), value, i.pos());
                });
                yield spreads == nd.spreads() && inits == nd.inits() ? nd
                        : new NewData(nd.typeName(), inits, spreads, nd.type(), nd.pos());
            }
            case Match m -> {
                Core scrutinee = atExpr.apply(m.scrutinee());
                List<Case> cases = each(m.cases(), c -> {
                    Core body = atExpr.apply(c.body());
                    return body == c.body() ? c
                            : new Case(c.caseTypes(), c.binding(), body, c.bindType(), c.pos());
                });
                yield scrutinee == m.scrutinee() && cases == m.cases() ? m
                        : new Match(scrutinee, cases, m.type(), m.pos());
            }
        };
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
                            java.util.function.UnaryOperator<NewData> onConstructionSlot) {
        return atSlots(e, onExprSlot, onNameSlot, onConstructionSlot);
    }

    /**
     * Applies {@code f} to each direct child of {@code e} — the read-only counterpart of
     * {@link #mapChildren}. Every slot is a child whatever kind it is, so a pass that asks what a
     * body reads reaches the binding a spread copies and the binding an application invokes without
     * knowing that either position exists.
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
