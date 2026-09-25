package souther.compiler.copied;

import souther.compiler.ast.Hir;
import souther.compiler.check.ConstEval;
import souther.compiler.execute.WrittenValue;
import souther.compiler.jvm.LinkageProjection;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;
import souther.compiler.types.WrittenTypeMeaning;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.function.Function;

/**
 * What a reader copies of a declaration, written so that two compiles of the declaration write the
 * same thing.
 *
 * <p>Taken of the declaration closed over its own module and no other — a helper or a value as
 * closing hands it to a reader, a type's invariant as its clauses closed the same way — and not of
 * the text a jar carries or a lowered method. The text answers to the author's layout, and a lowered
 * method to the call site the helper was expanded at.
 *
 * <p><b>Another module's definitions are written as what names them.</b> A value of another module
 * is its name; a helper of another module that closing expanded is its callee and the arguments it
 * was handed, and not the body the expansion copied. That body is a copy of that helper, held to
 * what that helper offers, and a reader copying this declaration copies it as well and records it
 * as such. Written in here instead, what this declaration is would move with what that helper is
 * held as, and the two would be compared under two different sayings of one thing: a constant
 * written another way is one constant, and the body it is written into would be another body.
 *
 * <p><b>What is left out, and why each.</b> Where the source put a term is where it was written and
 * not what it says. How a name was spelled — an alias, a qualification — is how it was reached, and
 * two spellings of one declaration are one reference. The number the compiler gave a binding is
 * minted as a copy is made, so a binding is written as the place it is bound at, counted from the
 * start of the definition: renaming a parameter or a {@code let} moves nothing here, and reading
 * another one does. A function handed to an expansion is bound nowhere in the tree, and is written
 * as the place it is first read. The origins a node carries count the constructs of a source and say where the
 * node came from.
 *
 * <p><b>What is kept.</b> Everything a run of the copy turns on: which node, the literal, the
 * operator, the field, the declaration a name reaches, the type a construct is written with, the
 * cases a match selects, and the children in the order the node holds them. A clause keeps its name,
 * which is what a refusal of the value says. The departures of an attempted construction are a
 * lookup by the clause that failed and not a sequence (spec §attempt-departures), so they are written in
 * the order of the clauses they answer, whatever order the source wrote them in.
 *
 * <p>What a helper's parameters are inferred as is not here, only what their author wrote of them
 * ({@link Hir.ParameterTypeFrom}). An inferred type follows from what is here and from the rules the
 * boundary revision stands for, so holding it again would be holding one fact twice.
 */
public final class CopiedIdentity {

    private final StringBuilder out = new StringBuilder();
    private final Map<BindingId, Integer> boundAt = new HashMap<>();
    /** The names read that nothing in what is written binds, where each was first read. */
    private final Map<BindingId, Integer> handedAt = new HashMap<>();
    /** The module the declaration belongs to: what is written of another is what names it. */
    private final String owner;
    /** Its helpers, as the module declared them. */
    private final Function<ValueName.Helper, Hir.FnDef> declaredHere;
    /** Whether a name bound outside what is written is a field of the declaration, which is what a
     *  clause reads. A helper or a value is closed, and one reading such a name is not. */
    private final boolean freeNamesAreFields;

    private CopiedIdentity(Owner owner, boolean freeNamesAreFields) {
        this.owner = owner.module();
        this.declaredHere = owner.declares();
        this.freeNamesAreFields = freeNamesAreFields;
    }

    /**
     * The module a declaration belongs to, and what it declares.
     *
     * @param module   the module
     * @param declares each helper of it as the module declared it, or null where it declares none of
     *                 that name — which is where what its author wrote of a helper expanded into the
     *                 declaration is read from
     */
    public record Owner(String module, Function<ValueName.Helper, Hir.FnDef> declares) {}

    /** A helper as its reader expands it: {@code closed}, with parameters, closed over the module
     *  that declares it. */
    public static CopyRecord helper(Hir.FnDef closed, Owner owner) {
        if (closed.params().isEmpty()) {
            throw new IllegalArgumentException("`" + closed.name() + "` is a value, and is copied"
                    + " as one");
        }
        CopiedIdentity writing = new CopiedIdentity(owner, false);
        writing.word("takes").count(closed.params().size());
        for (Hir.FnParam param : closed.params()) {
            writing.bind(param.binder());
            writing.parameterType(param);
        }
        writing.word("answers").type(closed.declaredReturn());
        writing.expr(closed.writtenBody());
        return new CopyRecord(CopyRecord.Form.CLOSED_HELPER, writing.out.toString());
    }

    /** A value as its reader copies its body: {@code closed}, taking nothing, closed over the
     *  module that declares it. */
    private static CopyRecord body(Hir.FnDef closed, Owner owner) {
        if (!closed.params().isEmpty()) {
            throw new IllegalArgumentException("`" + closed.name() + "` takes parameters, and is"
                    + " copied as a helper");
        }
        CopiedIdentity writing = new CopiedIdentity(owner, false);
        writing.word("answers").type(closed.declaredReturn());
        writing.expr(closed.writtenBody());
        return new CopyRecord(CopyRecord.Form.CLOSED_BODY, writing.out.toString());
    }

    /**
     * A value as its reader copies it: the constant it folds to, where a source can write that
     * constant, and its closed body otherwise.
     *
     * <p>A constant is held as what it is rather than as how it was written, so two bodies that
     * fold to one value are one copy. An exact ratio a division leaves is known at compile time and
     * has no literal to be held as, so a value folding to one is held as its body.
     *
     * @param closed what the value is, closed over {@code owner}
     * @param folded what it folds to, or empty where it is not a constant
     * @param owner  the module that declares it
     */
    public static CopyRecord value(Hir.FnDef closed, Optional<Object> folded, Owner owner) {
        WrittenValue constant = folded.map(ConstEval::asWritten).orElse(null);
        return constant != null
                ? new CopyRecord(CopyRecord.Form.CONSTANT, constant.written())
                : body(closed, owner);
    }

    /** A type's invariant as the types that include it check it: its clauses, closed over
     *  {@code owner}, in the order written. */
    public static CopyRecord clauses(List<Hir.InvariantClause> clauses, Owner owner) {
        CopiedIdentity writing = new CopiedIdentity(owner, true);
        writing.count(clauses.size());
        for (Hir.InvariantClause clause : clauses) {
            writing.optional(clause.name());
            writing.expr(clause.expr());
        }
        return new CopyRecord(CopyRecord.Form.CLAUSES, writing.out.toString());
    }

    // Every kind is named. A node added to the language stops the build here, which is where what it
    // means to a copy is decided.
    private void expr(Hir.Expr e) {
        switch (e) {
            case Hir.IntLit it -> word("int").word(String.valueOf(it.value()));
            case Hir.DecimalLit it -> word("decimal").word(it.value().toString());
            case Hir.StringLit it -> word("string").word(it.value());
            case Hir.BoolLit it -> word("bool").word(String.valueOf(it.value()));
            case Hir.Var it -> var(it);
            case Hir.FieldAccess it -> {
                word("field").word(it.name().canonical());
                expr(it.target());
            }
            case Hir.Apply it -> {
                word("apply").count(it.args().size());
                expr(it.function());
                it.args().forEach(this::expr);
            }
            case Hir.Binary it -> {
                word("binary").word(it.op().name());
                expr(it.left());
                expr(it.right());
            }
            case Hir.Neg it -> {
                word("neg");
                expr(it.operand());
            }
            case Hir.NewData it -> {
                word("new").name(it.typeName()).count(it.inits().size());
                for (Hir.FieldInit init : it.inits()) {
                    word(init.written().canonical());
                    expr(init.value());
                }
                count(it.spreads().size());
                it.spreads().forEach(this::var);
            }
            case Hir.Match it -> {
                word("match").count(it.cases().size());
                expr(it.scrutinee());
                for (Hir.Case one : it.cases()) {
                    count(one.caseTypes().size());
                    one.caseTypes().forEach(this::name);
                    List<Hir.Name> asserted =
                            one.unwrapAsserts() == null ? List.of() : one.unwrapAsserts();
                    count(asserted.size());
                    asserted.forEach(this::name);
                    if (one.binding() == null) {
                        word("unbound");
                    } else {
                        bind(one.binding());
                    }
                    expr(one.body());
                }
            }
            case Hir.If it -> {
                word("if");
                expr(it.cond());
                expr(it.then());
                expr(it.els());
            }
            case Hir.IfConstructed it -> {
                word("if constructed").count(it.els().size());
                expr(it.construct());
                bind(it.binder());
                expr(it.then());
                List<Hir.ElseArm> byClause = new ArrayList<>(it.els());
                byClause.sort(BY_CLAUSE);
                for (Hir.ElseArm arm : byClause) {
                    optional(arm.clause());
                    expr(arm.body());
                }
            }
            case Hir.ListLit it -> {
                word("list").count(it.elements().size());
                it.elements().forEach(this::expr);
            }
            case Hir.RowCollection it -> {
                word("row collection").count(it.elements().size());
                it.elements().forEach(this::expr);
            }
            case Hir.ListComp it -> {
                word("comprehension").count(it.guards().size());
                it.guards().forEach(this::expr);
                expr(it.element());
            }
            case Hir.LetIn it -> {
                word("let");
                expr(it.value());
                bind(it.binder());
                type(it.annotation());
                if (it.opens() == null) {
                    word("opens nothing");
                } else {
                    word("opens").name(it.opens());
                }
                expr(it.body());
            }
            // The types an expansion carries are its callee's signature, instantiated at this call
            // and with what the checker worked out written in beside what the author wrote, so
            // they are not read here. What the callee's author wrote is read off the callee.
            case Hir.Expansion it -> {
                word(isElsewhere(it.callee()) ? "expansion elsewhere" : "expansion")
                        .reference(it.callee()).count(it.bound().size());
                for (Hir.Bound bound : it.bound()) {
                    expr(bound.value());
                    bind(bound.binder());
                }
                count(it.given().size());
                for (Hir.Given given : it.given()) {
                    word(String.valueOf(given.applied()));
                    expr(given.value());
                }
                // What the expansion copied of another module's helper is that helper's, and is
                // held as that helper.
                if (!isElsewhere(it.callee())) {
                    signatureOf(it.callee());
                    expr(it.body());
                }
            }
            case Hir.Block it -> {
                word("block").count(it.params().size());
                it.params().forEach(this::bind);
                expr(it.body());
            }
            case Hir.Tuple it -> {
                word("tuple").count(it.elements().size());
                it.elements().forEach(this::expr);
            }
            case Hir.TupleGet it -> {
                word("tuple get").count(it.index()).count(it.arity());
                expr(it.tuple());
            }
            case Hir.Unreachable it -> word("unreachable").word(it.reason());
            // What a tree that runs is built of. Closing copies a value where it is named and builds
            // nothing in place, so meeting one means this was handed a tree nobody copies.
            case Hir.Materialised it -> throw new IllegalStateException(
                    "a copy is of a closed definition, which builds no value in place: " + it.value());
            case Hir.ValueBuild it -> throw new IllegalStateException(
                    "a copy is of a closed definition, which builds no value in place: " + it.value());
            case Hir.ValueInvocation it -> throw new IllegalStateException(
                    "a copy is of a closed definition, which calls no value's method: " + it.value());
        }
    }

    private void var(Hir.Var v) {
        if (!(v instanceof Hir.Var.Denoting denoting)) {
            throw new IllegalStateException("a copy is of a definition that checked, and `"
                    + v.written() + "` names nothing");
        }
        word("name");
        switch (denoting.denotes()) {
            case ValueName.Local local -> {
                Integer at = boundAt.get(local.id());
                if (at != null) {
                    word("bound").count(at);
                } else if (freeNamesAreFields) {
                    word("of the declaration").word(local.name());
                } else {
                    // A function handed to an expansion leaves no binding: the body reads the
                    // parameter it was handed to, and what stands behind that is the argument the
                    // expansion was given. Counted where it is first read, which is a place in the
                    // body and not a number the compiler minted for it.
                    Integer given = handedAt.computeIfAbsent(local.id(), _ -> handedAt.size());
                    word("handed").count(given);
                }
            }
            case ValueName.OfType type -> word("type").word(LinkageProjection.shown(type.type()));
            case ValueName.Builtin builtin -> word("builtin").word(builtin.name());
            case ValueName.Helper helper -> word("helper").word(helper.module()).word(helper.name());
            case ValueName.Behavior behavior ->
                    word("behavior").word(behavior.module()).word(behavior.name());
            case ValueName.Stdlib.Operation operation ->
                    word("library").word(operation.alias()).word(operation.name());
            case ValueName.Stdlib.Namespace namespace -> word("namespace").word(namespace.alias());
        }
    }

    /**
     * What the author of {@code callee}, a helper of the module written here, wrote of what it takes
     * and answers — or nothing, for a callee that is not one: a lambda a binding holds takes the
     * types of the parameters it was written with, and those are in its body, and one of the
     * language's is the same on every side of every artifact.
     */
    private void signatureOf(ValueName callee) {
        Hir.FnDef declared = callee instanceof ValueName.Helper helper
                && helper.module().equals(owner) ? declaredHere.apply(helper) : null;
        if (declared == null) {
            word("no signature here");
            return;
        }
        word("signature").count(declared.params().size());
        declared.params().forEach(this::parameterType);
        type(declared.declaredReturn());
    }

    /** What the author wrote of {@code param}'s type, and that the checker worked it out where the
     *  author wrote none. */
    private void parameterType(Hir.FnParam param) {
        if (param.typeFrom() == Hir.ParameterTypeFrom.INFERRED) {
            word("inferred");
        } else {
            type(param.type());
        }
    }

    /** Whether {@code callee} is a helper of a module other than the one written here, and other
     *  than the language's, which is the same on every side of every artifact. */
    private boolean isElsewhere(ValueName callee) {
        return callee instanceof ValueName.Helper helper && !helper.module().equals(owner)
                && !helper.isDeclaredByLanguage();
    }

    /** The departures of an attempted construction in the order of the clauses they answer: each
     *  named one by its clause, and the one for any clause after them. */
    private static final Comparator<Hir.ElseArm> BY_CLAUSE = Comparator
            .comparing((Hir.ElseArm arm) -> arm.clause().isEmpty())
            .thenComparing(arm -> arm.clause().orElse(""));

    /** What an expansion is of: the declaration its callee reaches, however it was spelled. */
    private CopiedIdentity reference(ValueName callee) {
        return word(callee instanceof ValueName.OfAModule of ? of.module() + "." + of.name()
                : callee instanceof ValueName.Stdlib library ? library.qualified()
                : callee.name());
    }

    private CopiedIdentity name(Hir.Name name) {
        Hir.Name.Denoting denoting = name.answered();
        if (denoting == null) {
            throw new IllegalStateException("a copy is of a definition that checked, and `"
                    + name.written() + "` names nothing");
        }
        return word(LinkageProjection.shown(denoting.type()));
    }

    private void bind(Hir.Binder binder) {
        int at = boundAt.size();
        boundAt.put(binder.binding(), at);
        word("binds").count(at);
    }

    private void type(Hir.RetType written) {
        if (written == null) {
            word("unwritten");
            return;
        }
        switch (written.meaning()) {
            case WrittenTypeMeaning.Settled settled -> word("type").word(shown(settled.type()));
            case WrittenTypeMeaning.NotAMember notAMember -> throw new IllegalStateException(
                    "a copy is of a definition that checked, and it writes a type that is not a"
                            + " member: " + notAMember.member());
        }
    }

    private static String shown(Type type) {
        return LinkageProjection.shown(type);
    }

    private void optional(Optional<String> word) {
        if (word.isPresent()) {
            word("named").word(word.get());
        } else {
            word("unnamed");
        }
    }

    private CopiedIdentity count(int n) {
        return word(String.valueOf(n));
    }

    /** One part, counted, so that no two sequences of parts are written the same. */
    private CopiedIdentity word(String part) {
        out.append(part.length()).append(':').append(part);
        return this;
    }
}
