package souther.compiler.core;

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
 * same types a second time. The one node with no type is the rounding mode of {@code divide}, a
 * built-in identifier the emitter reads by name rather than as a value (spec 18.3).
 *
 * <p>A surface-only node (a list comprehension) never appears — the Lower stage has already
 * rewritten it.
 */
public sealed interface Core {

    SourcePos pos();

    /** The type the checker decided for this expression (null only on a built-in identifier
     * the emitter reads by name — see the class comment). */
    Type type();

    record Int(long value, Type type, SourcePos pos) implements Core {}

    record Decimal(BigDecimal value, Type type, SourcePos pos) implements Core {}

    record Str(String value, Type type, SourcePos pos) implements Core {}

    record Bool(boolean value, Type type, SourcePos pos) implements Core {}

    record Var(String name, Type type, SourcePos pos) implements Core {}

    record Neg(Core operand, Type type, SourcePos pos) implements Core {}

    record FieldAccess(Core target, String field, Type type, SourcePos pos) implements Core {}

    record Binary(Ast.BinOp op, Core left, Core right, Type type, SourcePos pos) implements Core {}

    /** A call to a builtin, an injected behavior, or an intrinsic (a helper fn is already inlined). */
    record Call(String fn, List<Core> args, Type type, SourcePos pos) implements Core {}

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
    record IfConstructed(NewData construct, String binder, Core then, List<ElseArm> els, Type type,
                         SourcePos pos) implements Core {}

    /** One departure of an attempted construction: the clause it answers ({@link Optional#empty()}
     * for any failure) and the value taken. */
    record ElseArm(Optional<String> clause, Core body) {}

    /** A local binding. What the source wrote as its type — {@code let x: T = e} — is already in
     * {@code value}'s type: the checker pushed the annotation into the value when it typed it, so an
     * empty collection bound here materialises at the written type rather than a bottom (issue #71). */
    record LetIn(String name, Core value, Core body, Type type, SourcePos pos) implements Core {}

    /** A second-class block: a step passed to a recursive combinator, or an escaping lambda a {@code
     * let} binds (a closure). Kept as its own node until closure conversion gets an explicit Core form.
     * Its {@code type} is the {@link Type.FnOf} the checker gave it — the parameter types the context
     * fixed, and the body's result type. */
    record Block(List<String> params, Core body, Type type, SourcePos pos) implements Core {}

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

    record NewData(TypeName typeName, List<FieldInit> inits, List<String> spreads, Type type,
                   SourcePos pos) implements Core {}

    /** {@code bindType} is the type the case binding takes inside the arm — the case type a union
     * narrows to, or the element a {@code Some x} opens. */
    record Case(List<TypeName> caseTypes, String binding, Core body, Type bindType, SourcePos pos) {}

    record Match(Core scrutinee, List<Case> cases, Type type, SourcePos pos) implements Core {}

    /**
     * {@code e} with {@code f} applied to each of its immediate children, the node's own kind, type
     * and position kept. A Core-to-Core pass recurses through this rather than hand-copying every
     * node kind; being exhaustive over {@code Core}, a new node kind forces every such pass to
     * acknowledge it.
     */
    static Core mapChildren(Core e, java.util.function.UnaryOperator<Core> f) {
        return switch (e) {
            case Int x -> x;
            case Decimal x -> x;
            case Str x -> x;
            case Bool x -> x;
            case Var x -> x;
            case OptionNone x -> x;
            case Neg n -> new Neg(f.apply(n.operand()), n.type(), n.pos());
            case FieldAccess fa -> new FieldAccess(f.apply(fa.target()), fa.field(), fa.type(), fa.pos());
            case Binary b -> new Binary(b.op(), f.apply(b.left()), f.apply(b.right()), b.type(), b.pos());
            case Call c -> new Call(c.fn(), c.args().stream().map(f).toList(), c.type(), c.pos());
            case If iff -> new If(f.apply(iff.cond()), f.apply(iff.then()), f.apply(iff.els()),
                    iff.type(), iff.pos());
            case IfConstructed ic -> new IfConstructed((NewData) mapChildren(ic.construct(), f),
                    ic.binder(), f.apply(ic.then()),
                    ic.els().stream().map(arm -> new ElseArm(arm.clause(), f.apply(arm.body()))).toList(),
                    ic.type(), ic.pos());
            case LetIn li -> new LetIn(li.name(), f.apply(li.value()), f.apply(li.body()),
                    li.type(), li.pos());
            case Block b -> new Block(b.params(), f.apply(b.body()), b.type(), b.pos());
            case ListLit lit -> new ListLit(lit.elements().stream().map(f).toList(), lit.type(), lit.pos());
            case OptionSome s -> new OptionSome(f.apply(s.value()), s.type(), s.pos());
            case Tuple t -> new Tuple(t.elements().stream().map(f).toList(), t.type(), t.pos());
            case TupleGet tg -> new TupleGet(f.apply(tg.tuple()), tg.index(), tg.arity(),
                    tg.type(), tg.pos());
            case NewData nd -> new NewData(nd.typeName(),
                    nd.inits().stream()
                            .map(i -> new FieldInit(i.name(), f.apply(i.value()), i.pos())).toList(),
                    nd.spreads(), nd.type(), nd.pos());
            case Match m -> new Match(f.apply(m.scrutinee()),
                    m.cases().stream()
                            .map(c -> new Case(c.caseTypes(), c.binding(), f.apply(c.body()),
                                    c.bindType(), c.pos())).toList(),
                    m.type(), m.pos());
        };
    }

}
