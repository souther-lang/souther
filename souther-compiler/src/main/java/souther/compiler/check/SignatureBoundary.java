package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.DiagnosticCode;
import souther.compiler.diag.Region;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BoundaryMapKey;
import souther.compiler.types.LeafScalar;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;

import java.util.ArrayList;
import java.util.List;

/**
 * Builds what a behavior's boundary carries, refusing what it does not admit as it goes.
 *
 * <p>Validating and building are one walk because they are one question. Asked separately, the
 * checker's admitted set and the shapes a reader is handed agree only by coincidence, and nothing
 * says so: a rule relaxed on one side and not the other makes an ordinary compile succeed and the
 * reader raise. Here a shape exists because the walk that would have refused it did not, and a
 * signature that has one has been through every obligation.
 *
 * <p>Each structural position owns admissibility of the subtree under it, so there is no ordering
 * between rules to know. A {@code Map}'s key is asked whether it can be written as a boundary key,
 * whatever else it is; an element is asked what an element is asked. That is also what makes the
 * report the useful one — an optional in key position is refused for standing where a key goes, and
 * writing {@code Int} there instead does not help.
 *
 * <p>What replaces the ordering, where a signature is wrong in more than one place, is the order the
 * walk takes: the parameters as they are written, then the answer, and within a type from the
 * outside in. A precedence between rules would be a second thing to state and to keep true; the
 * traversal is one thing, and it is the one the author reads their own declaration in.
 *
 * <p>Reached only from {@link PipelineSigs#signatures}: this is how a {@link Sig} is made, not a
 * question about a type that anything may ask again.
 */
final class SignatureBoundary {

    private SignatureBoundary() {}

    /** The signature a declared behavior publishes — every parameter and its answer. */
    static Sig of(Ast.SpecBehavior spec, Symbols symbols) {
        List<BoundaryInput> ins = new ArrayList<>(spec.params().size());
        for (Ast.Param p : spec.params()) {
            Type t = TypeOps.successType(p.type(), symbols);
            ins.add(input(t, t, Where.param(p, spec.pos()), symbols));
        }
        Type out = TypeOps.successType(spec.ret(), symbols);
        return new Sig(ins, output(out, out, Where.output(spec.name(), spec.pos()), symbols));
    }

    /**
     * What a composition answers with. A composition's inputs are its first stage's, which arrive
     * already admitted; its output is a type nobody wrote — the last stage's answer merged with the
     * cases that left the main line — and is asked here for the first time.
     */
    static BoundaryOutput composedOutput(String behavior, SourcePos at, Type out, Symbols symbols) {
        return output(out, out, Where.output(behavior, at), symbols);
    }

    /**
     * What a parameter can arrive as.
     *
     * <p>{@code whole} is the parameter's own type, which the report about a function names: what is
     * refused is carrying one, and where in the type it sits is not what the author has to change.
     */
    private static BoundaryInput input(Type t, Type whole, Where where, Symbols symbols) {
        return switch (t) {
            case Type.Prim p -> new BoundaryInput.Scalar(scalar(p, where));
            case Type.Ref r -> new BoundaryInput.Nominal(nominal(r.name(), where, symbols));
            case Type.ListOf l -> new BoundaryInput.ListOf(input(l.element(), whole, where, symbols));
            case Type.SetOf s -> new BoundaryInput.SetOf(input(s.element(), whole, where, symbols));
            case Type.MapOf m -> new BoundaryInput.MapOf(mapKey(m.key(), where, symbols),
                    input(m.value(), whole, where, symbols));
            // A parameter names a single type, a named sum included, so the members of a union have
            // no name the far side can hold onto: the input and the output are separate for this.
            case Type.Union u -> throw union(u, where);
            case Type.OptionOf o -> throw optional(o, where);
            case Type.TupleOf _ -> throw tuple(where);
            case Type.FnOf _ -> throw function(whole, where);
            case Type.Erroneous _ -> throw new Unanswerable(where.pos());
            case Type.Var _, Type.MetaVar _, Type.Nothing _, Type.Never _ -> throw unwritable(t);
        };
    }

    /** What a behavior's answer can leave as. */
    private static BoundaryOutput output(Type t, Type whole, Where where, Symbols symbols) {
        return switch (t) {
            case Type.Prim p -> new BoundaryOutput.Scalar(scalar(p, where));
            case Type.Ref r -> new BoundaryOutput.Nominal(nominal(r.name(), where, symbols));
            case Type.Union u -> new BoundaryOutput.Cases(members(u, where, symbols));
            case Type.ListOf l -> new BoundaryOutput.ListOf(output(l.element(), whole, where, symbols));
            case Type.SetOf s -> new BoundaryOutput.SetOf(output(s.element(), whole, where, symbols));
            case Type.MapOf m -> new BoundaryOutput.MapOf(mapKey(m.key(), where, symbols),
                    output(m.value(), whole, where, symbols));
            case Type.OptionOf o -> throw optional(o, where);
            case Type.TupleOf _ -> throw tuple(where);
            case Type.FnOf _ -> throw function(whole, where);
            case Type.Erroneous _ -> throw new Unanswerable(where.pos());
            case Type.Var _, Type.MetaVar _, Type.Nothing _, Type.Never _ -> throw unwritable(t);
        };
    }

    /** The scalar a primitive stands for. {@code Raw} is written like one and is the language's own
     *  vocabulary rather than a model's, so it is refused as the name it is. */
    private static LeafScalar scalar(Type.Prim prim, Where where) {
        LeafScalar scalar = LeafScalar.of(prim);
        if (scalar == null) {
            throw foreignName(TypeName.primitive("Raw"), where);
        }
        return scalar;
    }

    /** A name the boundary carries: one a model declared, which is what a derived codec is for. The
     *  language declares vocabulary of its own — what a division by zero answers with, what a
     *  rounding takes — and each of those says what one of the language's operations can answer. */
    private static TypeName nominal(TypeName name, Where where, Symbols symbols) {
        if (!TypeOps.declaredByAModel(name, symbols)) {
            throw foreignName(name, where);
        }
        return name;
    }

    /** The members of the union a behavior answers with, each a name in what crosses. */
    private static List<TypeName> members(Type.Union union, Where where, Symbols symbols) {
        List<TypeName> members = new ArrayList<>(union.members().size());
        for (TypeName member : union.members()) {
            members.add(nominal(member, where, symbols));
        }
        return members;
    }

    /**
     * The witness a key position answers with. A map's external form is an object, whose keys are
     * strings, so this is the first thing asked of whatever stands there — an optional, a list or an
     * {@code Int} is refused for being unwritable as a key rather than for anything else it is.
     *
     * <p>A key that classifies is still the boundary's, so a name the language declares is refused
     * here as it is anywhere else in the shape.
     */
    private static BoundaryMapKey mapKey(Type key, Where where, Symbols symbols) {
        BoundaryMapKey classified = TypeOps.classifyConcreteMapKey(key, symbols);
        if (classified == null) {
            throw notAKey(key, where);
        }
        return switch (classified) {
            case BoundaryMapKey.StringNewtype n -> {
                nominal(n.name(), where, symbols);
                yield classified;
            }
            case BoundaryMapKey.UnitEnum e -> {
                nominal(e.name(), where, symbols);
                yield classified;
            }
            case BoundaryMapKey.Text _, BoundaryMapKey.Date _, BoundaryMapKey.DateTime _ -> classified;
        };
    }

    private static CompileException union(Type.Union u, Where where) {
        String shown = Type.show(u);
        return where.refusal(DiagnosticCode.E1312, "check.param.union",
                "parameter `" + where.name() + "` has an anonymous union type `" + shown
                        + "`; a parameter type must be a single named type — declare `data ... = "
                        + shown + "` and take that name (spec 8.6, 12.2)", shown);
    }

    /** A tuple is expression-level only: it has no external representation, so it cannot cross a
     *  decoder or an encoder. A tuple in a helper's signature is fine — it never touches a codec. */
    private static CompileException tuple(Where where) {
        return where.parameter()
                ? where.refusal(DiagnosticCode.E1311, "check.param.tuple",
                        "parameter `" + where.name() + "` is a tuple; a tuple has no external"
                                + " representation and cannot cross the boundary, so a behavior's"
                                + " input must be a named data")
                : where.refusal(DiagnosticCode.E1311, "check.output.tuple",
                        "behavior `" + where.name() + "` outputs a tuple; a tuple cannot cross the"
                                + " boundary, so a behavior's output must be a named data or a sum"
                                + " of them");
    }

    /** A function has no external representation at any depth, since one hides as easily inside a
     *  {@code List} or a {@code Map} as it stands on its own. */
    private static CompileException function(Type whole, Where where) {
        String shown = Type.show(whole);
        return where.parameter()
                ? where.refusal(DiagnosticCode.E1311, "check.param.function",
                        "parameter `" + where.name() + "` carries a function (" + shown
                                + "); a function has no external representation, so it cannot cross"
                                + " the boundary into a behavior", shown)
                : where.refusal(DiagnosticCode.E1311, "check.output.function",
                        "behavior `" + where.name() + "` outputs a function (" + shown
                                + "); a function has no external representation, so it cannot cross"
                                + " the boundary out of a behavior", shown);
    }

    /**
     * An optional does not stand in a behavior's boundary. A boundary carries the model's own
     * vocabulary, and absence there is owned by the data that holds it, on a {@code ?} field, or by
     * a sum the model names. What may not cross is the runtime representation of structural
     * optionality, which has no owner on the far side.
     */
    private static CompileException optional(Type.OptionOf o, Where where) {
        String shown = Type.show(o);
        return where.parameter()
                ? where.hinted(DiagnosticCode.E1313, "check.param.optional", "check.optional.hint",
                        "parameter `" + where.name() + "` carries an optional (" + shown + "); "
                                + OPTIONAL_ADVICE, shown)
                : where.hinted(DiagnosticCode.E1313, "check.output.optional", "check.optional.hint",
                        "the output of `" + where.name() + "` carries an optional (" + shown + "); "
                                + OPTIONAL_ADVICE, shown);
    }

    /** What to write instead, said of the optional rather than of the position it was found in: the
     *  optional a collection carries is not the behavior's own answer, so advice naming the
     *  behavior's type would be advice about something else. */
    private static final String OPTIONAL_ADVICE =
            "a model type has to own the absence where the optional stands — put it on a `?` field of"
                    + " a data, or name it as a case of a sum, which where the whole output is the"
                    + " optional is written directly as `-> A | Missing`";

    private static CompileException foreignName(TypeName foreign, Where where) {
        return where.parameter()
                ? where.hinted(DiagnosticCode.E1325, "check.param.foreignname",
                        "check.foreignname.hint",
                        "parameter `" + where.name() + "` takes `" + foreign.name() + "`, which the"
                                + " language declares rather than this model; " + FOREIGN_NAME_ADVICE,
                        foreign.name())
                : where.hinted(DiagnosticCode.E1325, "check.output.foreignname",
                        "check.foreignname.hint",
                        "`" + where.name() + "` answers `" + foreign.name() + "`, which the language"
                                + " declares rather than this model; " + FOREIGN_NAME_ADVICE,
                        foreign.name());
    }

    /** What to write instead. Said as declaring a type rather than as supplying a codec: the name is
     *  refused for whose vocabulary it is, and a codec for it would not change that. */
    private static final String FOREIGN_NAME_ADVICE =
            "declare this as a type of the model and write that at the boundary";

    private static CompileException notAKey(Type key, Where where) {
        String shown = Type.show(key);
        return where.parameter()
                ? where.hinted(DiagnosticCode.E1314, "check.map.key.param", "check.map.key.hint",
                        "parameter `" + where.name() + "` carries a Map keyed by " + shown + "; "
                                + TypeOps.MAP_KEY_RULE, shown)
                : where.hinted(DiagnosticCode.E1314, "check.map.key.output", "check.map.key.hint",
                        "behavior `" + where.name() + "` outputs a Map keyed by " + shown + "; "
                                + TypeOps.MAP_KEY_RULE, shown);
    }

    /**
     * A signature carrying a type no signature can be written with — a variable, a bottom, the type
     * of an expression that answers nothing. The spelling that would reach one is refused where it
     * is written, so arriving here is the compiler disagreeing with itself rather than anything a
     * reader of the module can act on.
     */
    private static IllegalStateException unwritable(Type t) {
        return new IllegalStateException(
                "`" + Type.show(t) + "` reached a behavior's boundary, which carries the types a"
                        + " model can write; the resolver and this disagree about what may be written");
    }

    /**
     * Where a refusal is reported and how it names what it refuses. A parameter is underlined where
     * it was written; an answer is reported on the behavior, which is what names it.
     */
    private record Where(boolean parameter, String name, Region region, SourcePos pos) {

        static Where param(Ast.Param p, SourcePos behavior) {
            return new Where(true, p.name(), p.written().region(), behavior);
        }

        static Where output(String behavior, SourcePos pos) {
            return new Where(false, behavior, null, pos);
        }

        Diagnostic.Builder diagnostic(DiagnosticCode code, String key) {
            Diagnostic.Builder builder = Diagnostic.of(code, key);
            return region == null ? builder.at(pos) : builder.at(region);
        }

        CompileException refusal(DiagnosticCode code, String key, String english, Object... rest) {
            return CompileException.of(diagnostic(code, key).args(args(rest)).build(), english);
        }

        CompileException hinted(DiagnosticCode code, String key, String hint, String english,
                                Object... rest) {
            return CompileException.of(
                    diagnostic(code, key).args(args(rest)).hint(hint).build(), english);
        }

        /** What the subject is called, then whatever the rule adds. Every one of these messages
         *  names the parameter or the behavior first. */
        private Object[] args(Object[] rest) {
            Object[] args = new Object[rest.length + 1];
            args[0] = name;
            System.arraycopy(rest, 0, args, 1, rest.length);
            return args;
        }
    }
}
