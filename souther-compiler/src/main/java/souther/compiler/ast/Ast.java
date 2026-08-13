package souther.compiler.ast;

import souther.compiler.diag.Region;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.MapKeyRepresentation;
import souther.compiler.types.LeafScalar;
import souther.compiler.types.ConstructionOrigin;
import souther.compiler.types.CoverageOrigin;
import souther.compiler.types.ReachName;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;
import souther.compiler.types.TypeReachName;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.Map;
import java.util.Optional;
import java.util.function.UnaryOperator;

/**
 * The slice-2 abstract syntax: a module of product {@code data} definitions with one or
 * more fields, each with an optional {@code invariant}, {@code decoder} (a single-value
 * {@code from Text|Int} form or a multi-field {@code from Object} form), and
 * {@code encoder} (a single Raw value or a {@code Object { ... }} form).
 */
public interface Ast {

    /** The source position of this node. Every record below provides it. */
    SourcePos pos();

    /**
     * A name a body binds: a parameter, a {@code let}, a lambda's parameter, a {@code match} arm's
     * binding. Every node below that introduces one holds this rather than a bare spelling, so what a
     * name under it means is the binding and not the text.
     *
     * <p>The two forms are the two states a binder is in. The parser writes {@link Written}, which is
     * the spelling and nothing more; {@code Resolve} answers it with {@link Bound}, which carries the
     * {@link BindingId} every name that resolves to it also carries. There is no third state and no
     * absent identity: a binder with an identity and a binder without one are different types, so a
     * reader cannot mistake one for the other, and nothing downstream tests for a missing one.
     */
    sealed interface Binder extends Ast {

        /** The name this binds and the occurrence of it that named it — the whole of what the
         * source says about this binding, kept as one value so a reader cannot pair the name with
         * somewhere it is not written. */
        WrittenName written();

        /** What the binding is called. A generated local is named after it; a diagnostic quotes
         * {@link WrittenName#quoted()} instead, which is what the author typed. */
        default String name() {
            return written().canonical();
        }

        /**
         * Where the author wrote this name, or null where the author wrote no name at all.
         *
         * <p>Not the same as {@link #pos()}, which is the form the binding came from: a {@code let}
         * statement starts at its keyword, a lambda's parameters share the lambda's start, and a
         * name a desugaring invented — the parameter {@code .field} becomes, the value a
         * {@code match} is held in — is written nowhere and only anchored somewhere.
         *
         * <p>A reader asking what is under a cursor has this and nothing else to compare against.
         * Anchoring one of those invented names at a form the author did write would put it under a
         * cursor on that form, and rename would then rewrite the source with a name no one can see.
         */
        default SourcePos namePos() {
            return written().authored() ? written().pos() : null;
        }

        /**
         * A binder read off a name the author wrote, taken from the name itself so its spelling and
         * its place cannot come from two different things.
         *
         * <p>There is no form here that takes the two apart. A caller holding a spelling and a
         * position separately is a caller nothing can stop from pairing a name with somewhere it is
         * not written, and this branch shipped that mistake three times: the parameter {@code .v}
         * desugars to, anchored at the {@code .}; a lambda's parameters, all anchored at the
         * lambda; a {@code match} arm's binding, anchored at the {@code |}. The parser reads a
         * binder off its token; a pass that needs a name of its own says {@link #desugared}.
         */
        static Binder of(Name written) {
            return new Written(written.name(), written.pos());
        }

        /**
         * A binder for a name no one wrote: what a desugaring binds a value to so that the form it
         * is rewriting keeps taking plain names. {@code anchor} is the form it came from, which is
         * where a complaint about it belongs and is not where its name is.
         */
        static Binder desugared(String name, SourcePos anchor) {
            return new Written(WrittenName.synthetic(name, anchor), anchor);
        }

        /**
         * The binding, for a reader that is asking which one this is.
         *
         * <p>A binder still {@link Written} here is a pass reading a body it was handed before
         * resolution answered it, which is a fault in the compiler rather than in the source, so it
         * is refused outright. This is the one place that says so.
         */
        default BindingId id() {
            if (this instanceof Bound bound) {
                return bound.binding();
            }
            throw new IllegalStateException("`" + name() + "` at " + pos()
                    + " was read as a binding before it was resolved");
        }

        /** A binder as the parser read it. */
        record Written(WrittenName written, SourcePos pos) implements Binder {

            @Override
            public String toString() {
                return name();
            }
        }

        /** A binder resolution answered, and the binding it introduces. */
        record Bound(WrittenName written, BindingId binding, SourcePos pos) implements Binder {

            public Bound {
                if (binding == null) {
                    throw new IllegalArgumentException("a bound binder is a binding: " + written);
                }
            }

            @Override
            public String toString() {
                return name();
            }
        }
    }

    /**
     * Mints the binders a pass writes into a body that has already been resolved.
     *
     * <p>Such a pass cannot leave a binder {@link Binder.Written}: nothing runs after it to answer
     * one. So it says which binding each is, and the bindings it makes belong to it — to
     * {@code owner} — rather than to the definition whose text it is writing into, which is what
     * keeps two of them apart when one body is written into twice.
     */
    final class Binders {

        private final BindingOwner owner;
        private int next;

        public Binders(BindingOwner owner) {
            this.owner = owner;
        }

        /** A binding nothing else has, under this pass's owner. A pass writes its own names, so
         * none of them is a name the author wrote. */
        public Binder binder(String name, SourcePos pos) {
            return new Binder.Bound(WrittenName.synthetic(name, pos),
                    new BindingId(owner, next++), pos);
        }
    }

    /**
     * A name that denotes a declared type, in both forms it has: {@code name} as the source writes
     * it — bare {@code 金額}, qualified {@code billing.金額}, or through an import alias — and
     * {@code denotes} as it resolves. Resolution happens once, in {@code Resolve}, before any check
     * runs; every name-bearing position in this tree carries one of these, so no later pass decides
     * for itself what a spelling means or whether a qualified one is allowed here (issue #177).
     *
     * <p>A check reads {@link #denotes()}, which is set on every name the resolve pass let through —
     * a name that denotes nothing is reported there and the compile stops, so nothing downstream sees
     * an unresolved one. {@link #written()} is the name, and is not what a report quotes: a bare and
     * a qualified spelling of one type are one name, and a decomposed and a composed spelling are
     * one name too, so neither says what the author typed. A report asks {@link WrittenName#quoted()}
     * and underlines {@link WrittenName#region()}.
     */
    record Name(WrittenName name, TypeName denotes) implements Ast {

        /** A name as the parser read it, before the resolve pass has said what it denotes. Only the
         * parser writes one: every other producer knows what it means and says so. The spelling is
         * the source's, not one a caller canonicalized on the way in — {@link WrittenName} is what
         * canonicalizes, so the name and the characters it was written with stay one value. */
        public static Name written(String spelling, SourcePos pos) {
            return new Name(WrittenName.of(spelling, pos), null);
        }

        /** A name a pass synthesized, already knowing what it denotes. It is written nowhere;
         * {@code pos} is what a complaint about it points at. The spelling is the declaration's own,
         * which is what a reference internal to a module reaches it by. */
        public static Name resolved(TypeName denotes, SourcePos pos) {
            return new Name(WrittenName.synthetic(denotes.name(), pos), denotes);
        }

        /**
         * The same, spelled as the module this is being written into reaches it.
         *
         * <p>For a pass whose output a person reads back: the declaration's own name is not what
         * every module writes, so a name synthesized with it quotes a spelling the reader cannot
         * write. What it denotes is the same either way.
         */
        public static Name reached(TypeReachName.Written type, SourcePos pos) {
            return new Name(WrittenName.synthetic(type.rendered(), pos), type.denotes());
        }

        /** The bare name this reaches its declaration by, whatever the source spelled. */
        public String written() {
            return name.canonical();
        }

        /** Where the name is written, or where a synthesized one is anchored. */
        public SourcePos pos() {
            return name.pos();
        }

        /** The same name, resolved to what it denotes. */
        public Name denoting(TypeName resolved) {
            return new Name(name, resolved);
        }

        @Override
        public String toString() {
            return written();
        }
    }

    /**
     * A whole source file: its public surface, imports, and definitions.
     *
     * <p>{@code exposedOutputs} maps an exposed composition behavior's name to the output signature written
     * in the {@code exposing} list ({@code exposing ( name : A | B )}, spec §declared-composition-output). An
     * exposed {@code >->} composition must have one, checked to match its inferred output (ADR-0024); other
     * exposed names carry no signature (their type is at the definition).
     *
     * <p>{@code fns} is what the source wrote, and it stays that at every stage. {@code takenOn} is
     * what the module took on to emit as methods of its own without having declared them, which is
     * two kinds of helper: a recursive one it reaches, which cannot be inlined and has to be lowered
     * somewhere, and a non-recursive one an {@code example} row applies, which a row runs rather than
     * expands (ADR-0077). Either may be declared by the standard library or by a module that
     * published it. Only {@code fns} is declared here, and no rule reads a name to tell the two apart
     * — {@code List.foldFrom} is reached under the library's alias and declared in
     * {@code souther.list}.
     *
     * <p>Two components rather than one list a later pass appends to. Appended, every reader asking
     * what the module declared got what it declared before {@link
     * souther.compiler.query.Shapes.Prepared} and that plus these after — the {@code exposing} check,
     * the value namespace a body is resolved against, and what the module publishes among them.
     *
     * <p>Whoever rebuilds a module carries {@code takenOn} across, and there is no constructor that
     * defaults it: a rebuild that quietly dropped it would put a module through codegen with the
     * methods its bodies call missing, which is the failure this separation is here to make
     * impossible. The arity says something has to be passed; that it is this module's own is what a
     * reader of the rebuild has to see, which is why every one of them names it.
     */
    record Module(String name,
                  List<String> exposing,
                  Map<String, RetType> exposedOutputs,
                  List<Import> imports,
                  List<Def> defs,
                  List<BehaviorDef> behaviors,
                  List<FnDef> fns,
                  List<FnDef> takenOn,
                  List<Example> examples,
                  List<Fake> fakes,
                  String exampleFileTarget,
                  SourcePos pos) implements Ast {}

    /**
     * {@code fake <injected> | (in) -> out | ...} — a test double for an injected behavior, used to
     * evaluate an example of a behavior that {@code depends on} it. The rows form an input→output
     * table matched by value equality; a {@code _ -> out} row is the default when no input matches
     * (otherwise a miss is an error). A fake produces no run-time class (it is a proxy at evaluation).
     */
    record Fake(String target, List<FakeRow> rows, SourcePos pos) implements Ast {}

    /** One fake row: input argument expressions mapped to an output, or the default ({@code inputs}
     * null / {@code isDefault} true). */
    record FakeRow(List<Expr> inputs, Expr output, boolean isDefault, SourcePos pos) implements Ast {}

    /** {@code with <dep> = <value>} on an example row — a value fake for an injected dependency
     * (a zero-argument behavior whose faked result is a constant). */
    record With(String dep, Expr value, SourcePos pos) implements Ast {}

    /**
     * {@code example <target> | row ...} — compile-time-checked examples for a behavior or a pure
     * helper. Whether written inline in the module or in an attached {@code examples for}
     * file, examples end up on {@link Module#examples()} (the compiler merges an attached file into
     * its target module). {@code exampleFileTarget} on a {@link Module} is non-null exactly when the
     * module was parsed from an {@code examples for <module>} file: it names the target and marks the
     * module as an example-only contribution, not a module of its own.
     */
    record Example(String target, List<ExampleRow> rows, SourcePos pos) implements Ast {}

    /**
     * One example row: an optional business description, the input argument expressions, and the
     * expected result. A bare {@link Var} expected asserts only the result arm (the case); a
     * {@link NewData}, a {@link Call} (a newtype constructor), or a literal asserts the whole value.
     */
    record ExampleRow(String description, List<Expr> inputs, List<With> withs, Expr expected,
                      SourcePos pos) implements Ast {}

    /**
     * {@code import a.b as B ( X, Y )} — an explicit, non-wildcard import (spec §modules).
     * {@code importedNames} are the names this import brings into scope bare; {@code alias} is the
     * qualifier the module is read under here, or null. Both parts are optional: a type is reachable
     * qualified whether or not it was imported (spec §modules), so an import with neither is just the
     * dependency written down.
     */
    record Import(String module, String alias, List<ImportedName> importedNames, SourcePos pos)
            implements Ast {

        public Import {
            importedNames = List.copyOf(importedNames);
        }

        /** The same names as the text they were written with — what a reader asking only what this
         * import brings in wants. Derived on each call rather than held: a record has its components
         * and no other field, and an import list is a handful of names. */
        public List<String> names() {
            return importedNames.stream().map(ImportedName::text).toList();
        }
    }

    /**
     * One name on an import list, and where it was written.
     *
     * <p>The position belongs to the name rather than to the line, because the name is what a reader
     * is told about. An import bringing in four names of which one is unused has something to say
     * about that one, and the line the four share cannot say which.
     */
    record ImportedName(WrittenName written) implements Ast {

        /** An entry a pass wrote, standing for a name no import list spells. */
        public ImportedName(String text, SourcePos pos) {
            this(pos == null ? WrittenName.synthetic(text, null) : WrittenName.of(text, pos));
        }

        /** The name the entry claims. */
        public String text() {
            return written.canonical();
        }

        /** Where the entry is written. */
        public SourcePos pos() {
            return written.pos();
        }
    }

    /**
     * A behavior definition — a specification, not an implementation (spec §behavior, §ast-nodes). It is either
     * a {@link SpecBehavior} (an input/output signature, with the body left to a matching
     * {@link FnDef} or to Java injection) or a {@link PipeBehavior} (a {@code >->} composition, which
     * is itself the implementation).
     */
    sealed interface BehaviorDef extends Ast permits SpecBehavior, PipeBehavior {

        /** The name this declares and the occurrence of it that declares it. Not {@link #pos()},
         * which is where the {@code behavior} keyword is. */
        WrittenName written();

        default String name() {
            return written().canonical();
        }

        SourcePos pos();
    }

    /**
     * {@code behavior name = (p1: T1, ...) -> R constructs A, B depends on C, D} — a signature with
     * no body (spec §behavior-io). A same-named {@link FnDef} is its implementation (§fn-declaration); with none, and
     * not a pipeline, it is a Java-injected behavior (§injected-behavior).
     *
     * <p>{@code dependsOn} lists the implementation-less behaviors the {@code fn} calls; they become
     * the {@code fn}'s trailing arguments and the injected fields of the generated class (§depends-on).
     */
    record SpecBehavior(WrittenName written,
                        List<Param> params,
                        RetType ret,
                        List<Name> constructs,
                        List<Var> dependsOn,
                        SourcePos pos) implements BehaviorDef {

        /** A behavior a pass wrote, named but written nowhere. */
        public SpecBehavior(String name, List<Param> params, RetType ret, List<Name> constructs,
                            List<Var> dependsOn, SourcePos pos) {
            this(WrittenName.synthetic(name, pos), params, ret, constructs, dependsOn, pos);
        }
    }

    /** A behavior parameter. Its type may be an anonymous union of cases (spec §unmarked-output). */
    record Param(WrittenName written, RetType type) implements Ast {

        /** A parameter a pass wrote. */
        public Param(String name, RetType type, SourcePos pos) {
            this(WrittenName.synthetic(name, pos), type);
        }

        /** What the parameter is called. */
        public String name() {
            return written.canonical();
        }

        /** Where the name is written. */
        public SourcePos pos() {
            return written.pos();
        }
    }

    /**
     * {@code behavior name = f >-> g >-> ... [-> A | B]} — a composition (spec §sequential-composition).
     * {@code declaredOut} is the optional trailing output declaration (§declared-composition-output): null
     * when absent (output is inferred), else the declared cases, which must match the inferred output exactly
     * (E1604).
     */
    record PipeBehavior(WrittenName written, List<Var> stages, RetType declaredOut, SourcePos pos)
            implements BehaviorDef {

        /** A composition a pass wrote, named but written nowhere. */
        public PipeBehavior(String name, List<Var> stages, RetType declaredOut, SourcePos pos) {
            this(WrittenName.synthetic(name, pos), stages, declaredOut, pos);
        }
    }

    /**
     * {@code fn name (a1, ...) = body} — a behavior's implementation (spec §fn-declaration). If a same-named
     * {@link SpecBehavior} exists, the parameter types come from it and the author writes none
     * ({@link FnParam#type()} is null, or read off a pattern; {@link FnParam#typeFromPattern()});
     * otherwise it is a helper {@code fn} that writes its own parameter types.
     *
     * <p>{@code body} is a single expression. The surface forms {@code let} and {@code guard} are
     * desugared by the parser into {@link LetIn} and {@link If} (spec §guard), so every later stage
     * sees one expression tree and has exactly one place where a value can be constructed.
     */
    /**
     * What stands to the right of a definition's {@code =}: the expression the author wrote, or —
     * in the reserved {@code souther} namespace only (spec §primitives) — the name of a shipped
     * kernel, {@code intrinsic "string.trim"}. One or the other, never neither, so a reader
     * switches rather than testing two fields for null.
     */
    sealed interface FnBody {
        /** A written body. */
        record Written(Expr expr) implements FnBody {
        }

        /** A named kernel; {@code key} is what the backend emits for. */
        record Intrinsic(String key) implements FnBody {
        }
    }

    /**
     * A {@code let} definition. A behavior fn or a helper carries a {@link FnBody.Written written}
     * body and no {@code declaredReturn}. A core intrinsic (spec §primitives) instead declares its
     * return type and names a primitive: {@code let trim (s: String): String = intrinsic
     * "string.trim"} — its body is {@link FnBody.Intrinsic}, written only in the {@code souther}
     * namespace. What the modifiers say is in {@link Modifiers}.
     *
     * <p>{@code declaredIn} is the module that wrote the {@code let}, and it is written once, where
     * the source is parsed. Every pass after that copies it. It is here because a module emits the
     * recursive helpers it reaches as its own methods, under the names it reaches them by, so from
     * that point a module's fns are declarations of several modules under one set of names — and
     * which module declared one decides what may be checked of it (ADR-0098). The name cannot answer
     * that: {@code List.foldFrom} is reached under the library's alias and declared in
     * {@code souther.list}.
     *
     * <p>Null says this is not a module-level declaration at all — a block standing where a function
     * goes, which has parameters and a body so that applying it expands like a call. It does not say
     * "from somewhere else": a helper this module took on to emit was written by some module and says
     * which, and every rule here reads that rather than the absence. Anything a later pass mints that
     * <em>is</em> a declaration says which module it belongs to, so that these stay one question.
     */
    record FnDef(WrittenName written, String declaredIn, List<FnParam> params,
                 RetType declaredReturn, FnBody body, Modifiers modifiers, SourcePos pos)
            implements Ast {
        /** A fn with no modifier (the common case; totality-checked if recursive, published). */
        public FnDef(WrittenName written, String declaredIn, List<FnParam> params,
                     RetType declaredReturn, FnBody body, SourcePos pos) {
            this(written, declaredIn, params, declaredReturn, body, Modifiers.NONE, pos);
        }

        /** A block standing where a function goes, which no module declares: a lambda a binding
         * holds, one handed to a function parameter. It has parameters and a body like a
         * declaration, which is what lets an application of it expand like a call, and it is
         * declared by nobody, which is what {@link #declaredIn} says of it. */
        public static FnDef lambda(String name, List<FnParam> params, RetType declaredReturn,
                                   FnBody body, SourcePos pos) {
            return new FnDef(WrittenName.synthetic(name, pos), null, params, declaredReturn, body,
                    Modifiers.NONE, pos);
        }

        /**
         * The same declaration under the name a module reaches it by.
         *
         * <p>The one way a declaration is renamed. A module emits a recursive helper it reaches as
         * one of its own methods, under the name it reaches it by ({@code List.foldFrom},
         * {@code maths.spin}), and that name is not where the declaration came from:
         * {@code List.foldFrom} is reached under the library's alias and declared in
         * {@code souther.list}, so the module it came from cannot be read back out of it. Renaming
         * here carries {@link #declaredIn} across rather than restating it, so no caller is in a
         * position to pair a name with an origin that is not its own.
         */
        public FnDef reachedAs(String name) {
            return new FnDef(WrittenName.synthetic(name, pos), declaredIn, params, declaredReturn,
                    body, modifiers, pos);
        }

        /** The same declaration with {@code replacement} in place of its body. */
        public FnDef withBody(FnBody replacement) {
            return new FnDef(written, declaredIn, params, declaredReturn, replacement, modifiers,
                    pos);
        }

        /** What the fn is called. */
        public String name() {
            return written.canonical();
        }

        /** Whether {@code module} is the module that declared this. Asked of the declaration, so a
         * helper another module published answers for the module that wrote it however the module
         * reading it happens to reach it. A lambda is declared by no module and answers no. */
        public boolean declaredBy(String module) {
            return declaredIn != null && declaredIn.equals(module);
        }

        /** Whether the definition opts out of the totality check. */
        public boolean partial() {
            return modifiers.partial();
        }

        /** Whether the definition is kept out of the module's published surface. */
        public boolean isPrivate() {
            return modifiers.isPrivate();
        }

        /** The expression the author wrote. Asked from positions an intrinsic cannot reach — a
         *  user module, or a helper already known written — which is said here rather than by a
         *  silent null. */
        public Expr writtenBody() {
            return switch (body) {
                case FnBody.Written w -> w.expr();
                case FnBody.Intrinsic _ -> throw new IllegalStateException(
                        "`" + name() + "` is an intrinsic and has no written body");
            };
        }
    }

    /**
     * The words written before a {@code let}. {@code partial} opts a recursive helper out of the
     * totality check (spec §fn-declaration). {@code isPrivate} keeps the definition out of the
     * module's published surface: it is a core privilege, written only in the reserved
     * {@code souther} namespace, so the standard library can carry an implementation helper that
     * no caller can name.
     *
     * <p>They travel together because they are both answers to "how was this {@code let} written",
     * and because two adjacent booleans in a constructor call read as neither.
     */
    record Modifiers(boolean partial, boolean isPrivate) {
        public static final Modifiers NONE = new Modifiers(false, false);
    }

    /** A {@code fn} parameter: a name, and a type only when the {@code fn} is a helper (spec §fn-declaration).
     * A helper's parameter type may be a function type {@link FnType}; a behavior fn's parameter
     * carries no type ({@code type} is null). {@code typeFromPattern} marks a type read off a
     * constructor pattern in parameter position rather than written beside the name — a behavior's
     * implementation may write the pattern, and its type still comes from the behavior. */
    record FnParam(Binder binder, RetType type, boolean typeFromPattern) implements Ast {
        /** A parameter whose type, if any, the author wrote (the common case). */
        public FnParam(Binder binder, RetType type) {
            this(binder, type, false);
        }

        public String name() {
            return binder.name();
        }

        /** The name and the occurrence of it that binds this parameter. */
        public WrittenName written() {
            return binder.written();
        }

        @Override
        public SourcePos pos() {
            return binder.pos();
        }
    }

    /**
     * One term of a written type: a reference to a named type, or a function type. A type position
     * admits either, so what a name means does not depend on where it was written; whether a
     * function may stand in a given position is decided by what that position requires of a type,
     * not by the grammar.
     */
    sealed interface TypeTerm extends Ast permits TypeRef, FnType {}

    /** A function type {@code (A, ...) -> B}. Its parameters and result are whole types, so a
     * function may take one and may return one. */
    record FnType(List<RetType> params, RetType result, SourcePos pos) implements TypeTerm {}

    /** A written type: one term, or the unmarked sum of several (spec §unmarked-output). */
    record RetType(List<TypeTerm> cases, SourcePos pos) implements Ast {

        /** The function type this stands for, or null when it is not a lone function type. A sum of
         * a function with anything else is not one, and has no case to be told apart by. */
        public FnType asFn() {
            return cases.size() == 1 && cases.get(0) instanceof FnType fn ? fn : null;
        }
    }

    /** A top-level data definition: product, sum, or unit. */
    sealed interface Def extends Ast permits Data, SumData, UnitData {

        /**
         * The name this declares, and the occurrence of it that declares it.
         *
         * <p>Where the name is written is not where the declaration starts — {@code data} comes
         * first. A reader asking what a cursor is on has only the name to compare against, and a
         * declaration that answers from its keyword answers about the keyword. It is
         * {@link WrittenName#authored() unwritten} for a declaration nobody wrote: a unit data a
         * construction implied.
         */
        WrittenName written();

        /** What the declaration is called. */
        default String name() {
            return written().canonical();
        }

        /** Where the name is written, or null where nobody wrote it. */
        default SourcePos namePos() {
            return written().authored() ? written().pos() : null;
        }

        SourcePos pos();
    }

    /**
     * A product data definition: included data (flattened) plus its own fields.
     *
     * <p>{@code newtype} marks the explicit newtype form {@code data X = Y} (spec §newtype): a single
     * implicit field named {@code value} of type {@code Y}, encoded as bare {@code Y} instead of an
     * object. Everything else (construction {@code X { value: v }}, access {@code x.value},
     * invariant on {@code value}) is the same as a one-field product; only the external
     * representation differs.
     */
    record Data(WrittenName written,
                boolean newtype,
                List<Name> includes,
                List<Field> fields,
                List<InvariantClause> invariants,
                Optional<DecoderDef> decoder,
                Optional<EncoderDef> encoder,
                SourcePos pos) implements Def {}

    /**
     * One {@code invariant} clause, in the order it is written. Every clause must hold, so the
     * clauses of a declaration mean their conjunction; they are kept apart because a failure is
     * reported as one of them — the first that does not hold (spec §invariant-declaration).
     *
     * <p>{@code name} is what an attempted construction's departure arm and a boundary issue call the
     * rule. An unnamed clause is enforced exactly as before it could be named: nothing can tell it
     * apart from the type's other unnamed clauses, so it aborts inside the domain and fails the decode
     * outside it without saying which rule it was.
     */
    record InvariantClause(Optional<String> name, Expr expr, SourcePos pos) implements Ast {

        /** A clause no name was written for. */
        public static InvariantClause unnamed(Expr expr) {
            return new InvariantClause(Optional.empty(), expr, expr.pos());
        }

        /** The same clause over a rewritten expression — what a stage that rewrites expressions
         * produces, so a rewrite never drops the name the rest of the compiler classifies by. */
        public InvariantClause with(Expr rewritten) {
            return new InvariantClause(name, rewritten, pos);
        }
    }

    /** A sum data definition {@code data X = A | B | ...} with optional discriminate decoder/encoder. */
    record SumData(WrittenName written,
                   List<Name> cases,
                   Optional<Discriminate> decoder,
                   Optional<SumEncoder> encoder,
                   SourcePos pos) implements Def {}

    /** {@code encoder discriminate on "key" { Case -> "tag" ... }} — the inverse of discriminate. */
    record SumEncoder(String key, List<EncVariant> variants, SourcePos pos) implements Ast {}

    record EncVariant(Name caseType, String tag, SourcePos pos) implements Ast {}

    /** A unit data definition {@code data U} with no fields. */
    record UnitData(WrittenName written, SourcePos pos) implements Def {

        /** A unit data a construction implied — declared nowhere the author wrote. */
        public UnitData(String name, SourcePos pos) {
            this(WrittenName.synthetic(name, pos), pos);
        }
    }

    /** {@code decoder from Object discriminate on "key" { "tag" -> Case.decoder ... }} */
    record Discriminate(String key, List<Variant> variants, SourcePos pos) implements Ast {}

    record Variant(String tag, Name caseType, SourcePos pos) implements Ast {}

    /** A field: a role name and its type. */
    record Field(WrittenName written, TypeTerm type) implements Ast {

        /** A field a pass wrote — the implicit {@code value} of a newtype. */
        public Field(String name, TypeTerm type, SourcePos pos) {
            this(WrittenName.synthetic(name, pos), type);
        }

        /** What the field is called. */
        public String name() {
            return written.canonical();
        }

        /** Where the name is written. */
        public SourcePos pos() {
            return written.pos();
        }
    }

    /**
     * A named type reference, optionally with one type argument (e.g. {@code List<T>}). When
     * {@code name} is null and {@code tupleElems} is non-null the ref is a tuple type
     * {@code (A, B, ...)} (ADR-0036), written only in a helper/stdlib signature. A {@code Map<K, V>}
     * reuses {@code tupleElems} to carry its key type (a single element) while {@code name} is
     * {@code "Map"} and {@code arg} is the value type (ADR-0040).
     *
     * <p>The two forms are the two states a reference is in, as {@link Binder}'s are. The parser
     * writes {@link Written}, which is the spelling and the shape around it; {@code Resolve} answers
     * it with {@link Denoting}, which carries the type it stands for. There is no third state and no
     * absent type: a reference that stands for a type and one that has not been read are different
     * types, so nothing downstream tests for a missing one.
     *
     * <p>The type is decided once (issue #177), which is what keeps a later reader from resolving a
     * written type a second time — and from having to know which module the reference was written
     * in, which is what a second resolution needed to get right.
     */
    sealed interface TypeRef extends TypeTerm permits TypeRef.Written, TypeRef.Denoting {

        /** The name as it is spelled, or null where the reference names none — a tuple, or a type a
         * pass settled and left no surface for. */
        WrittenName written();

        /** The single type argument, as {@code List<T>} has. */
        TypeTerm arg();

        /** A tuple's elements, or the single key type a {@code Map} carries (ADR-0040). */
        List<TypeTerm> tupleElems();

        /** Where a reference with no name to start at begins. */
        SourcePos anchor();

        /** A reference the source wrote, read off the characters that spell it. */
        static TypeRef written(WrittenName written, TypeTerm arg, List<TypeTerm> tupleElems) {
            return new Written(written, arg, tupleElems, null);
        }

        /** A reference a pass wrote before resolution runs, named but written nowhere — {@code T?}
         * becoming {@code Option<T>}, a {@code Map} carrying its key. */
        static TypeRef written(String name, TypeTerm arg, List<TypeTerm> tupleElems, SourcePos pos) {
            return new Written(name == null ? null : WrittenName.synthetic(name, pos), arg,
                    tupleElems, pos);
        }

        /** An ordinary (non-tuple) reference a pass wrote before resolution runs. */
        static TypeRef written(String name, TypeTerm arg, SourcePos pos) {
            return written(name, arg, null, pos);
        }

        /**
         * A reference nobody wrote: it carries what it denotes and no surface text. A helper
         * parameter whose type its body settles is written back as one (issue #178) — the type is
         * decided, and there is no source it stands for. Everything downstream of {@code Resolve}
         * reads {@link #denotes()}, so a reference with a decided type is as good as a written one.
         */
        static TypeRef of(Type type, SourcePos pos) {
            return new Denoting(null, null, null, type, pos);
        }

        /** The name this reference stands for, or null where it names none. */
        default String name() {
            return written() == null ? null : written().canonical();
        }

        /** Where the reference starts. A named one starts where its name does; {@code anchor} is
         * for the ones that have no name to start at, which is why it is not asked otherwise: two
         * places for one reference is two places that can disagree. */
        default SourcePos pos() {
            return written() == null ? anchor() : written().pos();
        }

        /** A tuple type is the nameless form; a named ref that also carries {@code tupleElems}
         *  (a {@code Map} carrying its key) is not a tuple. */
        default boolean isTuple() {
            return written() == null && tupleElems() != null;
        }

        /**
         * The type this stands for, for a reader that is asking what it is.
         *
         * <p>A reference still {@link Written} here is a pass reading a type it was handed before
         * resolution answered it, which is a fault in the compiler rather than in the source, so it
         * is refused outright. This is the one place that says so.
         */
        default Type denotes() {
            if (this instanceof Denoting denoting) {
                return denoting.type();
            }
            throw new IllegalStateException("`" + name() + "` at " + pos()
                    + " was read as a type before it was resolved");
        }

        /** The same reference, resolved. */
        default TypeRef denoting(Type type) {
            return new Denoting(written(), arg(), tupleElems(), type, anchor());
        }

        /** A reference as the parser read it. */
        record Written(WrittenName written, TypeTerm arg, List<TypeTerm> tupleElems,
                       SourcePos anchor) implements TypeRef {

            @Override
            public String toString() {
                return name() == null ? "(tuple)" : name();
            }
        }

        /** A reference resolution answered, and the type it stands for. */
        record Denoting(WrittenName written, TypeTerm arg, List<TypeTerm> tupleElems, Type type,
                        SourcePos anchor) implements TypeRef {

            public Denoting {
                if (type == null) {
                    throw new IllegalArgumentException(
                            "a reference that denotes is a type: " + written);
                }
            }

            @Override
            public String toString() {
                return name() == null ? String.valueOf(type) : name();
            }
        }
    }

    /** The kind of primitive Raw a single-value decoder reads / an encoder writes. */
    enum RawKind { TEXT, INT, BOOL, DECIMAL, DATE, TIME, DATETIME, INSTANT }

    // --- decoders ---

    sealed interface DecoderDef extends Ast permits PrimDecoder, ObjectDecoder, NewtypeDecoder {}

    /** {@code decoder from Text|Int as <input> { <stmts> <construct> }} (single value). */
    record PrimDecoder(RawKind from,
                       Binder input,
                       List<DecStmt> stmts,
                       Construct result,
                       SourcePos pos) implements DecoderDef {

        public String inputName() {
            return input.name();
        }
    }

    /** {@code decoder from Object { <binds> <construct> }} (multi-field, accumulating). */
    record ObjectDecoder(List<Bind> binds, Construct result, SourcePos pos) implements DecoderDef {}

    /**
     * A newtype {@code data X = Y} over a non-primitive {@code Y} (spec §newtype): the whole input is
     * decoded by {@code inner} (a reference to {@code Y}'s decoder), and the result wrapped in
     * {@code X}. {@code X}'s external representation is {@code Y}'s — an object or a discriminated
     * sum, not {@code {value: ...}}.
     */
    record NewtypeDecoder(DecRef inner, Binder input, Construct result, SourcePos pos)
            implements DecoderDef {

        public String inputName() {
            return input.name();
        }
    }

    /** One field an object decoder reads: the key it is found under, how the value there is read,
     *  and the name the construction below refers to it by. Built by {@code Deriver}; no source
     *  writes one. */
    record Bind(Binder binder, String key, DecRef ref, SourcePos pos) implements Ast {

        public String name() {
            return binder.name();
        }
    }

    /** The decoder referenced by a bind: a primitive, another data's {@code .decoder}, or a list. */
    sealed interface DecRef extends Ast permits DecRef.Bare, OptionDecRef {

        /** A reference that is not an optional. What the distinction is for is the one position that
         *  requires it: what an optional decodes. Absence has one form wherever it stands, so an
         *  optional under an optional has two forms for three values and is not written
         *  (spec {@code [#what-has-no-external-representation]}). */
        sealed interface Bare extends DecRef
                permits PrimDecRef, DataDecRef, ListDecRef, SetDecRef, MapDecRef {}
    }

    record PrimDecRef(LeafScalar kind, SourcePos pos) implements DecRef.Bare {}

    record DataDecRef(Name typeName, SourcePos pos) implements DecRef.Bare {}

    /** {@code list(<elementDecRef>)} */
    record ListDecRef(DecRef element, SourcePos pos) implements DecRef.Bare {}

    /** {@code set(<elementDecRef>)} — a list decoder deduplicated into a Set on decode (ADR-0009). */
    record SetDecRef(DecRef element, SourcePos pos) implements DecRef.Bare {}

    /** An optional decoder. Under a key, a missing key or {@code null} is {@code None}; standing as
     *  an element or a map's value, where there is no key to be missing, {@code null} is the whole
     *  of it. Either way a present value decodes through {@code element}. */
    record OptionDecRef(DecRef.Bare element, SourcePos pos) implements DecRef {}

    /** A {@code Map<K, T>} decoder: each object value is decoded with {@code value}, and each of the
     * object's string keys through {@code key}.
     *
     * <p>The key is a {@link MapKeyRepresentation} rather than a {@code DecRef}: a key position holds one of
     * the representations the boundary admits, and nothing else — not a list, not an option — so the
     * type says as much and a reader that switches on it needs no arm for what cannot be there. It is
     * also the classification the checker already made, carried here rather than worked out again. */
    record MapDecRef(DecRef value, MapKeyRepresentation key, SourcePos pos) implements DecRef.Bare {}

    /** A primitive field decoder kind. */
    /** A statement in a single-value decoder body. */
    sealed interface DecStmt extends Ast permits Let {}

    record Let(Binder binder, Expr value, SourcePos pos) implements DecStmt {

        public String name() {
            return binder.name();
        }
    }

    /**
     * The construction a decoder ends in: {@code TypeName { field: expr, ... }}, one value per field.
     *
     * <p>Not an expression, and not what a body writes — a decoder is derived or written in the codec
     * grammar, and nothing there spreads. A construction a body writes is {@link NewData}.
     */
    record Construct(Name typeName, List<FieldInit> inits, SourcePos pos) implements Ast {}

    /** One {@code field: expr} (or shorthand {@code field}) inside a record literal. */
    /** {@code field: value} in a construction. */
    record FieldInit(WrittenName written, Expr value) implements Ast {

        /** An initialiser a pass wrote — a derived encoder's, a newtype's implicit {@code value}. */
        public FieldInit(String name, Expr value, SourcePos pos) {
            this(WrittenName.synthetic(name, pos), value);
        }

        /** The field this fills. */
        public String name() {
            return written.canonical();
        }

        /** Where the field name is written. */
        public SourcePos pos() {
            return written.pos();
        }

        /**
         * The same initialiser over a rewritten value.
         *
         * <p>The field's occurrence is the author's and survives a rewrite of what fills it. Naming
         * the field again — which every rewrite that took {@link #name()} and a position did — puts a
         * spelling where an occurrence was, and what is lost is the only record of where the author
         * wrote it: a report about the field then underlines as many characters as the name has,
         * starting where it starts, which is the same thing until it is not.
         */
        public FieldInit withValue(Expr rewritten) {
            return rewritten == value ? this : new FieldInit(written, rewritten);
        }
    }

    // --- encoders ---

    record EncoderDef(Binder self, RawExpr result, SourcePos pos) implements Ast {

        public String selfName() {
            return self.name();
        }
    }

    /** A Raw-building expression. */
    sealed interface RawExpr extends Ast
            permits TextRaw, IntRaw, BoolRaw, DecimalRaw, IsoTextRaw, ObjectRaw, EncodeRaw, ListEnc,
                    SetEnc, OptionRaw, MapEnc {}

    /** Encodes a {@code Map<K, T>} to a {@code Raw.Object}, each value via {@code elem} and each key
     * to its bare string through {@code key} — the representation the checker admitted it as, closed
     * for the reason {@link MapDecRef}'s is. */
    record MapEnc(Expr source, EncElem elem, MapKeyRepresentation key, SourcePos pos) implements RawExpr {}

    /** Encodes an optional field: {@code None} becomes {@code Raw.Null}, {@code Some(v)} encodes
     * {@code v} via {@code inner}, which reads the unwrapped value bound to {@code elemVar}. */
    record OptionRaw(Expr access, RawExpr inner, Binder elem, SourcePos pos) implements RawExpr {

        public String elemVar() {
            return elem.name();
        }
    }

    record TextRaw(Expr arg, SourcePos pos) implements RawExpr {}

    record IntRaw(Expr arg, SourcePos pos) implements RawExpr {}

    record BoolRaw(Expr arg, SourcePos pos) implements RawExpr {}

    /** Encodes a {@code Decimal} field to a {@code Raw.Decimal}. */
    record DecimalRaw(Expr arg, SourcePos pos) implements RawExpr {}

    /** Encodes a {@code Date}/{@code DateTime} field to a {@code Raw.Text} via its ISO8601 form. */
    record IsoTextRaw(Expr arg, SourcePos pos) implements RawExpr {}

    record ObjectRaw(List<RawEntry> entries, SourcePos pos) implements RawExpr {}

    /** {@code TypeName.encode(expr)} — encode a nested data value to Raw. */
    record EncodeRaw(Name typeName, Expr arg, SourcePos pos) implements RawExpr {}

    /** {@code list(expr, <elemEnc>)} — encode a {@code List<T>} to a Raw.List. */
    record ListEnc(Expr source, EncElem elem, SourcePos pos) implements RawExpr {}

    /** Encodes a {@code Set} as a JSON array: the set is listed, then each element encoded. */
    record SetEnc(Expr source, EncElem elem, SourcePos pos) implements RawExpr {}

    /** How to encode a list/set/map element: a primitive, another data's {@code .encode}, or another
     * collection — a collection may hold a collection ({@code Map<String, List<商品ID>>}), so the
     * element encoder nests as deeply as the type does. */
    sealed interface EncElem extends Ast permits EncElem.Bare, OptionElemEnc {

        /** An element encoder that is not an optional, for the reason {@link DecRef.Bare} carries. */
        sealed interface Bare extends EncElem
                permits PrimEnc, DataEnc, ListElemEnc, SetElemEnc, MapElemEnc {}
    }

    record PrimEnc(LeafScalar kind, SourcePos pos) implements EncElem.Bare {}

    record DataEnc(Name typeName, SourcePos pos) implements EncElem.Bare {}

    /** A {@code List<T>} element, each {@code T} encoded by {@code elem}. */
    record ListElemEnc(EncElem elem, SourcePos pos) implements EncElem.Bare {}

    /** A {@code Set<T>} element: listed, then each element encoded by {@code elem}, as {@link SetEnc}
     * does for a field. */
    record SetElemEnc(EncElem elem, SourcePos pos) implements EncElem.Bare {}

    /** A {@code Map<K, V>} element, each value encoded by {@code value} and each key by {@code key},
     * as {@link MapEnc} does for a field. */
    record MapElemEnc(EncElem value, MapKeyRepresentation key, SourcePos pos) implements EncElem.Bare {}

    /** An optional standing where there is no key to omit — a collection's element, a map's value.
     * {@code None} is written {@code null} and {@code Some(v)} through {@code elem}
     * (spec {@code [#absence-is-written-as-null]}). A field's optional is {@link OptionRaw}, which
     * omits its key instead. */
    record OptionElemEnc(EncElem.Bare elem, SourcePos pos) implements EncElem {}

    record RawEntry(String key, RawExpr value, SourcePos pos) implements Ast {}

    // --- expressions ---

    sealed interface Expr extends Ast
            permits IntLit, DecimalLit, StringLit, BoolLit, Var, FieldAccess, Apply, Binary, Neg,
                    NewData, Match, If, IfConstructed, ListLit, ListComp, LetIn, Expansion, Block,
                    Tuple, TupleGet, Unreachable {

        /**
         * The stretch of source this expression was written over, or null where no one wrote it.
         *
         * <p>Not {@link #pos()}, and not derivable from it. A position is where a report about this
         * node is anchored, and an anchor is chosen for the node it is about: a binary operation is
         * anchored at its operator and a field read at its field, because that is where a complaint
         * about either belongs. Neither is where the expression begins, so a region built from an
         * anchor and a width starts inside what the author wrote however the width is arrived at.
         *
         * <p>Read off the tree the parser built and carried from there. Working it out later means
         * measuring the node — its name's length, its value's length, the token kinds it is made of
         * — and a measurement is a claim about the value rather than about the file. The two agree
         * until the source spells something the value does not keep: an escape, a decomposed
         * spelling, a leading zero, a pair of parentheses.
         *
         * <p>Null rather than a zero-width region at the anchor. A node a lowering minted was
         * written nowhere, and a report about it has nothing to underline — which is a different
         * answer from underlining no characters at a place the author's cursor could be.
         */
        Region region();

        /**
         * Where a report about this expression points: the characters it was written over, or the
         * point it is anchored at where no one wrote it.
         *
         * <p>The choice between two answers already held, and not a third answer worked out from
         * either. A node a lowering minted has somewhere a complaint about it belongs and nothing to
         * underline, and that is what a point is — a place with no characters claimed at it, which
         * the renderer draws as the one caret it draws for anything it cannot measure.
         *
         * <p>Null only where the node has neither, which is a report with nowhere to point.
         */
        default Region reportedAt() {
            Region written = region();
            if (written != null) {
                return written;
            }
            return pos() == null ? null : Region.point(pos());
        }
    }

    /**
     * {@code unreachable "reason"} — the point the model says cannot arise (spec §match).
     *
     * <p>It answers no value, so it has no type of its own to check against the position it is
     * written in: it types at {@code Never} and fits whatever is expected. The reason is a literal
     * rather than an expression so that the compiler and a reader both have it without running the
     * model; at run time it is the message the abort carries.
     */
    record Unreachable(String reason, SourcePos pos, Region region) implements Expr {}

    /**
     * {@code x -> expr}, or {@code (acc, x) -> expr} — a block (spec §blocks).
     *
     * <p>Second-class: it may only be an argument, never a value that is returned, stored in a
     * field, or bound by {@code let}. The parser only accepts one in an argument position, and
     * because it cannot escape, the backend inlines it rather than building a closure.
     */
    record Block(List<Binder> params, Expr body, SourcePos pos, Region region) implements Expr {

        /** A block whose parameters are names no one wrote — what a desugaring builds. A block the
         * author wrote is built from binders of its own, because its parameters are written one by
         * one and the block's own position is where the first of them starts at best. */
        public static Block desugared(List<String> params, Expr body, SourcePos pos, Region region) {
            List<Binder> binders = new ArrayList<>();
            for (String p : params) {
                binders.add(Binder.desugared(p, pos));
            }
            return new Block(binders, body, pos, region);
        }

        /** How the parameters were written, in order. */
        public List<String> paramNames() {
            List<String> names = new ArrayList<>();
            for (Binder p : params) {
                names.add(p.name());
            }
            return names;
        }
    }

    /**
     * {@code let name = value} followed by {@code body} — what a body's {@code let} desugars to
     * (spec §let). Nesting the rest of the body inside keeps {@code value} from being evaluated
     * when an enclosing {@code if} (a desugared {@code guard}) takes the other branch.
     *
     * <p>{@code declaredType} is the binding's declared type, if any, and {@code annotated} says
     * where it came from. A source annotation ({@code let x: T = e}) is pushed into {@code value}
     * as its expected type and checked against it, so a value only context can type — an empty
     * collection — is pinned at the binding. A type supplied by helper inlining (the parameter's
     * declared type, bound to the argument at the call site) is not: the argument's own type and
     * the call-site check already cover it.
     */
    record LetIn(Binder binder, Expr value, RetType declaredType, boolean annotated, Name opens,
                 Expr body, SourcePos pos, Region region) implements Expr {
        /** An ordinary {@code let x = e}: the bound name takes {@code e}'s inferred type. */
        public LetIn(Binder binder, Expr value, Expr body, SourcePos pos, Region region) {
            this(binder, value, null, false, null, body, pos, region);
        }

        /** A binding for a name no one wrote: what a desugaring holds a value in. A binding the
         * source wrote is built from a binder of its own, because a {@code let} statement starts at
         * its keyword and the name it binds is somewhere after it. */
        public LetIn(String name, Expr value, Expr body, SourcePos pos, Region region) {
            this(Binder.desugared(name, pos), value, null, false, null, body, pos, region);
        }

        /** A binding carrying an inlined helper parameter's declared type. */
        public LetIn(Binder binder, Expr value, RetType declaredType, Expr body, SourcePos pos,
                     Region region) {
            this(binder, value, declaredType, false, null, body, pos, region);
        }

        /** {@code let x: T = value} — a binding the source annotated. */
        public static LetIn annotated(Binder binder, Expr value, RetType type, Expr body,
                                      SourcePos pos, Region region) {
            return new LetIn(binder, value, type, true, null, body, pos, region);
        }

        public String name() {
            return binder.name();
        }

        /**
         * One layer of a constructor pattern: the binding holds the whole value and {@code opens}
         * names the newtype the pattern claims it is. A {@code match} arm gets that claim checked by
         * the exhaustiveness pass, which knows the scrutinee's cases; a binding has no such pass
         * behind it, so the name is carried here for the checker to hold against the value's type.
         */
        public static LetIn opening(String name, Expr value, Name opens, Expr body, SourcePos pos,
                                    Region region) {
            return new LetIn(Binder.desugared(name, pos), value, null, false, opens, body, pos,
                    region);
        }

        /** The type the source wrote on this binding, or null when it wrote none. An annotation is an
         * ordinary type (a function type belongs only in a helper's parameter), so this is the one
         * place that narrows {@code declaredType}, and a carrier from inlining never reads as one. */
        public RetType annotation() {
            return annotated && declaredType instanceof RetType rt ? rt : null;
        }
    }

    /**
     * One application of a non-recursive helper, with the callee's body in place of the call.
     *
     * <p>It is one node rather than the bindings it becomes because a signature is one statement.
     * {@code emptyLike (xs: List<'a>) : List<'a>} says the result holds what the argument held, and
     * that is said by the two occurrences of {@code 'a} being one variable. Written out as a binding
     * per argument, each carrying its own declared type, there is nothing left saying the two
     * occurrences were ever the same — and a signature position that leaves no binding at all, which
     * the declared return and an unapplied function parameter both do, has nowhere to say anything.
     * Holding the whole instantiation here is what makes the rule hold however the callee was
     * written.
     *
     * <p>{@code application} names this one expansion, and the variables of {@code declaredReturn},
     * {@code bound} and {@code given} are that application's ({@link Type.MetaVar}). Two calls of one
     * helper are two applications and two sets of variables; a call inside an expansion is another.
     *
     * <p>{@code body} is the callee's, with each parameter read as the binding or the function it was
     * given. It is the only slot holding code that runs: what {@code given} holds is already inside
     * it wherever the callee applies it, and is kept here so the signature can be read against it.
     */
    record Expansion(ValueName callee, BindingOwner application, List<Bound> bound,
                     List<Given> given, RetType declaredReturn, Expr body,
                     SourcePos pos, Region region) implements Expr {

        /**
         * The same expansion as the nested bindings it writes — for a reader whose question is only
         * about what flows where.
         *
         * <p>Not every reader is asking about the signature. What an invariant may be discharged
         * from is a question about which value reached which position, and to that reader an
         * expansion is a name bound to an argument and a body reading it, exactly as a {@code let}
         * the author wrote is. Reading it as one keeps those readers saying about a call what they
         * say about the code it stands for.
         */
        public Expr asBindings() {
            Expr out = body;
            for (int i = bound.size() - 1; i >= 0; i--) {
                Bound b = bound.get(i);
                out = new LetIn(b.binder(), b.value(), b.declaredType(), out, pos, region);
            }
            return out;
        }
    }

    /** {@code e} with every expansion in it read as the bindings it writes ({@link
     * Expansion#asBindings}), at every depth. */
    public static Expr asBindings(Expr e) {
        Expr through = e instanceof Expansion ex ? ex.asBindings() : e;
        return mapChildren(through, Ast::asBindings, name -> name);
    }

    /** A value argument. It becomes a binding, so the body reads a name rather than the argument's
     * text, and the callee's declared type for it comes along. */
    record Bound(Binder binder, RetType declaredType, Expr value) {}

    /**
     * A function argument. It leaves no binding, so what the signature said about it reaches a
     * reader only from here.
     *
     * <p>{@code arrivesAs} is what the argument is declared as where it comes from, where this
     * expansion can see that. The two declarations are what a boundary holds — what this callee
     * wants of the position, and what the function handed to it is — and reading them against each
     * other is what the boundary is for.
     *
     * <p>{@code applied} is whether the callee's body still reaches it. Where it does, the body is
     * where this argument is typed and what the signature said is checked by that application, as it
     * is for a function written in place. Where it does not — the callee named a function parameter
     * and never used it — the body says nothing about it at all, and this is the only place it can
     * be held to the type the callee declared for it.
     */
    record Given(RetType declaredType, Expr value, boolean applied, RetType arrivesAs) {}

    /** A list literal {@code [e1, e2, ...]} (one or more elements of the same type). */
    record ListLit(List<Expr> elements, SourcePos pos, Region region) implements Expr {}

    /** A guard-only comprehension {@code [element | guard, ...]}: the element is included when
     * every guard holds, giving a 0-or-1 element list (spec §stdlib-list, conditional accumulation).
     *
     * <p>{@code origin} names the comprehension, and the fork each guard lowers to is derived from it
     * ({@link CoverageOrigin#lowered}) rather than minted where the lowering runs — so a comprehension
     * inside a helper answers the same whichever call site expanded it. */
    record ListComp(Expr element, List<Expr> guards, CoverageOrigin origin, SourcePos pos,
                    Region region) implements Expr {}

    /** A tuple {@code (e1, e2, ...)} of two or more values (ADR-0036), an expression-level value
     * that never crosses the data/behavior boundary. Opened with a {@code let (x, y) = t} destructure. */
    record Tuple(List<Expr> elements, SourcePos pos, Region region) implements Expr {}

    /** Reads the {@code index}-th element of a tuple; what a {@code let (x, y) = t} destructure lowers
     * a field read to. Not written in source — the parser produces it from a tuple pattern. {@code arity}
     * is the pattern's name count, so the checker rejects a tuple of a different size (ADR-0036). */
    record TupleGet(Expr tuple, int index, int arity, SourcePos pos, Region region) implements Expr {}

    /** {@code if cond then a else b} — both branches must have the same type (spec §if).
     *
     * <p>{@code origin} is the fork the author wrote, kept through every rewrite and every copy an
     * expansion makes, so the arms of one {@code if} are one obligation however many times a helper
     * holding it is called ({@link CoverageOrigin}). */
    record If(Expr cond, Expr then, Expr els, CoverageOrigin origin, SourcePos pos, Region region)
            implements Expr {}

    /**
     * {@code if T(v) as x then a else b} — an attempted construction, and what
     * {@code guard T(v) as x else b} desugars to. {@code construct}'s invariant decides the branch:
     * holding, the value is built and {@code binder} names it in {@code then}; failing, {@code els} is
     * taken and no value is built. The binder is scoped to {@code then} alone, which is why this is a
     * node of its own rather than a condition {@code If} would have to introspect — a plain
     * {@code If}'s condition never binds.
     *
     * <p>A construction here does not abort, so it is exempt from the possible-violation warning
     * (spec §invariant-discharge); a violation the compiler *decides* is still reported, because then no branch was
     * ever in question.
     *
     * <p>{@code construct} is an {@link Expr} rather than a {@link NewData} because the newtype
     * spelling {@code T(v)} is a {@link Call} until {@link souther.compiler.check.NewtypeDesugar}
     * rewrites it — the same reason nothing else in the AST can name a construction by type either.
     * That it is one, and that its type carries an invariant to attempt, are checked once the names
     * are resolved.
     */
    record IfConstructed(Expr construct, Binder binder, Expr then, List<ElseArm> els,
                         CoverageOrigin origin, SourcePos pos, Region region) implements Expr {

        /** The attempt whose failure is not told apart: one arm, naming no clause. */
        public IfConstructed(Expr construct, Binder binder, Expr then, Expr els,
                             CoverageOrigin origin, SourcePos pos, Region region) {
            this(construct, binder, then, List.of(ElseArm.any(els)), origin, pos, region);
        }

        /** The same, as the parser read it. */

        /** How the binding was written. */
        public String binderName() {
            return binder.name();
        }

        /** Whether the failure is departed from per clause, rather than by one value for any of them. */
        public boolean mapsClauses() {
            return els.size() > 1 || els.get(0).clause().isPresent();
        }
    }

    /**
     * One departure of an attempted construction: the value taken when {@code clause} is the invariant
     * clause that did not hold, or when any of them did not ({@code clause} empty — the {@code else e}
     * form, and the {@code | _ -> e} that stands for the clauses carrying no name).
     *
     * <p>The arms are a lookup by clause, not a sequence: which arm is taken is decided by the failing
     * clause, so the order they are written in has no effect. Which clause fails is decided by the
     * order the clauses are declared in (spec §invariant-declaration).
     */
    record ElseArm(Optional<String> clause, Expr body, SourcePos pos) implements Ast {

        /** The arm taken for any failure — what {@code else e} and {@code | _ -> e} both mean. */
        public static ElseArm any(Expr body) {
            return new ElseArm(Optional.empty(), body, body.pos());
        }

        /** The same arm over a rewritten body, so a rewriting stage keeps the clause it answers. */
        public ElseArm with(Expr rewritten) {
            return new ElseArm(clause, rewritten, pos);
        }
    }

    /** {@code match scrutinee { case Case as x -> body ... }} over a sum type. {@code origin} is the
     * fork the author wrote; see {@link If}. */
    record Match(Expr scrutinee, List<Case> cases, CoverageOrigin origin, SourcePos pos,
                 Region region) implements Expr {}

    /**
     * One {@code match} case: {@code case A | B ... [as x] -> body} (spec §match). {@code caseTypes}
     * holds one case name, or several joined by {@code |} (an or-pattern, spec §match). With one case,
     * {@code x} binds that case's type; with several, it binds the scrutinee's sum type, since no
     * single case type fits all alternatives.
     */
    /**
     * {@code unwrapAsserts} are the inner newtype names written in a constructor-destructuring
     * pattern {@code X(Y(s))} — {@code [Y]} here (the case {@code X} is in {@code caseTypes}, the
     * bound variable {@code s} is dropped). {@code null} when the pattern is not a constructor
     * destructure; an empty list is the single-layer form {@code X(v)}. The {@code TypeChecker}
     * verifies every opened layer is a newtype and that each name matches the layer it opens.
     */
    record Case(List<Name> caseTypes, Binder binding, Expr body, List<Name> unwrapAsserts,
                SourcePos pos) implements Ast {
        public Case(List<Name> caseTypes, Binder binding, Expr body, SourcePos pos) {
            this(caseTypes, binding, body, null, pos);
        }

        /** How the binding was written, or null where the arm binds nothing. */
        public String bindingName() {
            return binding == null ? null : binding.name();
        }
    }

    /**
     * {@code TypeName { ..src, field: expr, ... }} used as an expression (construction in a behavior).
     *
     * <p>A spread names a value like any other position, so it carries what that name resolves to: a
     * binding in force wins over a declaration here as everywhere else, and a reader downstream must
     * not go back to matching the spelling against the module's own definitions.
     */
    /**
     * A construction. {@code origin} says where it came from: written here, or carried in by a
     * published body or by a value this body named.
     *
     * <p>Expansion makes the two look alike: a construction spliced in from another body is the same
     * node the reader's own would be, and the permission check reading that body would ask the
     * reader to answer for it. So the construction says where it came from. Every rebuild of this
     * node carries it — the component has no default, which is what stops a pass from quietly
     * dropping it and turning a carried construction back into the reader's own.
     */
    record NewData(Name typeName, List<FieldInit> inits, List<Var> spreads,
                   ConstructionOrigin origin, SourcePos pos, Region region) implements Expr {

        /** The same construction, carried into a reader by {@code module}'s published body. */
        public NewData publishedBy(String module) {
            return new NewData(typeName, inits, spreads, origin.publishedIn(module), pos, region);
        }

        /** The same construction, carried into a body by a value that body named. */
        public NewData carriedByValue() {
            return new NewData(typeName, inits, spreads, origin.carriedByValue(), pos, region);
        }
    }

    record IntLit(long value, SourcePos pos, Region region) implements Expr {}

    record DecimalLit(java.math.BigDecimal value, SourcePos pos, Region region) implements Expr {}

    /** Unary minus {@code -operand} on an Int or Decimal (spec §an-operator-takes-the-types-it-is-defined-for). */
    record Neg(Expr operand, SourcePos pos, Region region) implements Expr {}

    record StringLit(String value, SourcePos pos, Region region) implements Expr {}

    record BoolLit(boolean value, SourcePos pos, Region region) implements Expr {}

    /**
     * A name used as a value — the one representation the surface AST has for one. {@code written}
     * is how the source writes it (bare {@code price}, qualified {@code billing.price}, or through
     * an import alias) and {@code denotes} is what it names, answered once during resolution; a
     * reader asks that rather than deciding for itself whether the spelling is a local, a unit data
     * or something the language provides. What {@link Name} is for a type.
     *
     * <p>It stands in two kinds of slot, which differ in what may replace it:
     *
     * <ul>
     *   <li>an expression slot, where any expression may stand — an argument, a field's value, the
     *       thing an {@code if} tests;</li>
     *   <li>a name slot, where only another name may — a construction's spread {@code T { ..base }},
     *       which copies the fields of what the name stands for and so has nothing to evaluate.</li>
     * </ul>
     *
     * <p>Both are children: {@link #forEachChild} reaches them, so a pass that asks about names sees
     * a spread without knowing spreads exist. {@link #mapChildren} takes the two slots as separate
     * operators, so a rewrite cannot put an expression where only a name may stand. A pass that does
     * substitute an expression for a name — the inliner — binds it ahead of the construction and
     * spreads the binding.
     *
     * <p>A name that denotes nothing was reported where it was written and carries
     * {@link ValueName.Unresolved}, so a reader downstream never has a spelling to match and never
     * repeats the report.
     */
    record Var(WrittenName written, ValueName denotes, ReachName reachedAs,
               Region region) implements Expr {

        /**
         * A name that has been resolved has both answers or neither.
         *
         * <p>Both, or neither: a name the parser read is unanswered on both counts, and a name
         * resolution answered is answered on both. Nothing in between is a state — the pair comes
         * from one pass, which has both or has not run.
         *
         * <p>Refused rather than allowed to stand, because what a name reaches is asked of a table
         * and a table answers a key it has not got with silence. A rewrite that carried the
         * denotation across and dropped the reach name would leave a reference that resolves to a
         * declaration and reaches nothing, and the first reader of it would read the spelling
         * instead — which is what this pair was separated out to stop. The other half is the same
         * defect facing the other way: a reach name beside no denotation is a key nothing says the
         * meaning of, and {@link ReachName#of} is where one would have to come from.
         *
         * <p>The region is the expression's and the name's is {@code written}'s, and they part
         * company only where the author wrapped the name in something the tree does not keep:
         * {@code (price)} is one expression written over nine characters and one name written over
         * five. So the one has to hold the other. A region that did not would be a claim that the
         * name is written somewhere this expression is not, which no source can produce.
         */
        public Var {
            if ((denotes == null) != (reachedAs == null)) {
                throw new IllegalArgumentException("`" + written.canonical() + "` denotes "
                        + denotes + " and is reached as " + reachedAs
                        + "; a name has both answers or neither");
            }
            if (written.region() != null && region == null) {
                throw new IllegalArgumentException("`" + written.canonical()
                        + "` is written somewhere and the expression it is was written nowhere");
            }
            if (!Region.encloses(region, written.region())) {
                throw new IllegalArgumentException("`" + written.canonical()
                        + "` is written outside the expression it is");
            }
        }

        /** A name as the parser read it, before resolution has said what it denotes or how this
         * module reaches it. */
        public Var(String spelling, SourcePos pos) {
            this(WrittenName.of(spelling, pos), null, null);
        }

        /** A name standing as an expression over exactly the characters that spell it — every one
         * but a name the author parenthesized. */
        public Var(WrittenName written, ValueName denotes, ReachName reachedAs) {
            this(written, denotes, reachedAs, written.region());
        }

        /**
         * A name a pass already knows the meaning of, written where the source writes it.
         *
         * <p>The reach name is given rather than worked out here. A pass writing a name into a body
         * either has one in hand — it is rewriting a name that already carried it — or knows which
         * module's body it is writing into, and neither is something this constructor can see. Worked
         * out from the spelling it would be the very derivation the carried value exists to remove.
         */
        public Var(String spelling, ValueName denotes, ReachName reachedAs, SourcePos pos) {
            this(WrittenName.of(spelling, pos), denotes, reachedAs);
        }

        /**
         * A name a pass wrote in place of one the author wrote, standing where that one stood.
         *
         * <p>{@code spelling} is the pass's — a helper qualified by the module that declares it, so
         * that a body carried out of its module goes on reaching the same declaration. The
         * characters at {@code pos} spell what the author put there, which is not this, so the name
         * is written nowhere and only the expression has a place: the region is the one the name it
         * replaced was read over.
         */
        public static Var respelled(String spelling, ValueName denotes, ReachName reachedAs,
                                    SourcePos pos, Region region) {
            return new Var(WrittenName.synthetic(spelling, pos), denotes, reachedAs, region);
        }

        /** The bare name this reaches its declaration by, whatever the source spelled. */
        public String name() {
            return written.canonical();
        }

        /** Where the name is written. */
        public SourcePos pos() {
            return written.pos();
        }

        /**
         * The bare name this reaches its declaration by, whatever the source spelled.
         *
         * <p>Every name here has been through resolution by the time anything reads it, including
         * one that denotes nothing — that is an answer too. A name with no answer at all means a
         * tree reached a reader without being resolved, which would put this back to matching
         * spellings, so it says so rather than falling back to the spelling.
         */
        public String bare() {
            if (denotes == null) {
                throw new IllegalStateException("`" + name() + "` was never resolved");
            }
            return denotes.name();
        }

        /** Whether this name denotes nothing — reported where it was written. */
        public boolean unresolved() {
            return denotes instanceof ValueName.Unresolved;
        }

        /**
         * A read of something bound in the body, as a pass that put the binding there writes it.
         *
         * <p>A pass that runs after resolution says what it means rather than leaving a spelling for
         * a reader to work out, so it is given the binder it is reading and answers with that
         * binding. There is no way to write one of these without having the binding in hand.
         */
        public static Var local(Binder binder, SourcePos pos) {
            ValueName.Local local = new ValueName.Local(binder.name(), binder.id());
            return new Var(WrittenName.synthetic(binder.name(), pos), local,
                    new ReachName.Bare(binder.name()));
        }

        /** A read of a name a desugaring minted, at the form it is rewriting. Written nowhere: the
         * characters at {@code anchor} spell whatever the author put there, which is not this. */
        public static Var desugared(String name, SourcePos anchor) {
            return new Var(WrittenName.synthetic(name, anchor), null, null);
        }

        /**
         * The name of the declaration this reference reaches — what a table keyed by a declaration's
         * name is looked up with. The reading counterpart of {@link Apply#reaches()}:
         * {@link #name()} is the name the source writes, which an import may have let go without its
         * qualifier.
         *
         * <p>Never the spelling. A name that reached a reader without being resolved has no answer
         * to this, and it says so rather than handing back the characters — which is the same rule
         * {@link #bare()} is under, and for the same reason: an import lets a name be written
         * without its qualifier, so the spelling misses in the very table this is asked for, and a
         * table answers a key it has not got with silence. Every pass that writes a reference of its
         * own says what it means (ADR-0067), so there is no tree downstream of resolution for the
         * fallback to have been for.
         */
        public String reaches() {
            if (reachedAs == null) {
                throw new IllegalStateException("`" + name() + "` was never resolved");
            }
            return reachedAs.rendered();
        }

        /**
         * The same name, denoting {@code resolved} and reached as {@code reachedAs}.
         *
         * <p>The two answers together, because resolution gives them together and they are the two
         * halves of one question: which declaration this reaches, and under what name it reaches it
         * from here. Handed over separately, a caller could pair one name's denotation with another's
         * reach name, and nothing would say so.
         */
        public Var denoting(ValueName resolved, ReachName reachedAs) {
            return new Var(written, resolved, reachedAs, region);
        }

        /** The same name denoting {@code resolved}, reached as it already was — for a pass that
         * changes what a name says about where its construction came from and not which declaration
         * it reaches. */
        public Var denoting(ValueName resolved) {
            return new Var(written, resolved, reachedAs, region);
        }

        @Override
        public String toString() {
            return name();
        }
    }

    /**
     * {@code target.field} — a field taken off a value, or (until {@code Resolve} folds it) a member
     * taken off a namespace. {@code name} is the field's own occurrence, and {@code pos} is where
     * that occurrence is: a report about a field read is about the field, so it is anchored there
     * and not where the read begins. Where it begins is {@code region}'s to say, and the two differ
     * by however the target was written.
     */
    record FieldAccess(Expr target, WrittenName name, SourcePos pos, Region region) implements Expr {

        /** An access a pass wrote: the field is named but written nowhere, so there is nothing for a
         * report to underline. */
        public FieldAccess(Expr target, String field, SourcePos pos) {
            this(target, WrittenName.synthetic(field, pos), pos, null);
        }

        /**
         * An access standing where the author wrote something else — a copy of a body from another
         * source, stamped at the place it was carried to.
         *
         * <p>The field is named and written nowhere, the occurrence it was read from being in the
         * file this copy is no longer being read against. The characters are still somebody's, and
         * they are whatever stands at {@code region} in the file this is read in. The counterpart of
         * {@link Var#respelled}, for the same reason.
         */
        public static FieldAccess restamped(Expr target, String field, SourcePos at, Region over) {
            return new FieldAccess(target, WrittenName.synthetic(field, at), at, over);
        }

        /** The same access over a rewritten target. The field's occurrence and the stretch of source
         * the read was written over are the author's and survive a rewrite of what it reads from —
         * naming the field again here would put a spelling where an occurrence was. */
        public FieldAccess withTarget(Expr rewritten) {
            return rewritten == target ? this : new FieldAccess(rewritten, name, pos, region);
        }

        /** The field this reads. */
        public String field() {
            return name.canonical();
        }
    }

    /**
     * A function applied to arguments. {@code function} is the thing being applied, and it is an
     * expression like any other: what is applied is what it answers, not how the application was
     * written.
     *
     * <p>Applying a name is the common case and has its own constructors and readers below. A name
     * carries what it denotes — a helper, a library function, an injected behavior, a function-typed
     * binding, or the type a newtype construction wraps — answered once during resolution.
     */
    record Apply(Expr function, List<Expr> args, ConstructionOrigin origin, String appliedAs,
                 SourcePos pos, Region region) implements Expr {

        /** Applying whatever {@code function} is, with nothing standing in for what the source
         * wrote — every application but one a lowering rewrote. */
        public Apply(Expr function, List<Expr> args, ConstructionOrigin origin, SourcePos pos,
                     Region region) {
            this(function, args, origin, null, pos, region);
        }

        /**
         * Applying a name a pass chose, at the form it stands in, saying what that name means and
         * how the body being written into reaches it.
         *
         * <p>{@code fn} is a spelling and not an occurrence — a library name a rewrite reached for,
         * a fixture's constructor, a value rendered back out of what was computed — so the applied
         * name is written nowhere and the characters at {@code pos} spell whatever the author put
         * there. A name the author applied is passed as the {@link Var} it is, which is where its
         * occurrence is; building one from a spelling and a position measures the spelling at the
         * anchor, and the two are the same number only until they are not.
         *
         * <p>The denotation and the reach name are taken and not optional. A pass writing an
         * application either has them or is writing a name it has not resolved, and the second is
         * what ADR-0067 rules out: the spelling would be read back downstream by whatever the
         * reading module happens to mean by it. Only the parser leaves a callee unanswered, and it
         * builds the {@link Var} for itself.
         *
         * <p>{@code region} is the application's and is not handed to the callee. What the callee
         * covers is its own — a rewrite that puts another name in a call leaves the arguments where
         * they are, so a report about what is applied would otherwise underline them too. A caller
         * that has the callee's extent builds the {@link Var} itself and passes it.
         */
        public Apply(String fn, ValueName denotes, ReachName reachedAs, List<Expr> args,
                     ConstructionOrigin origin, SourcePos pos, Region region) {
            this(Var.respelled(fn, Objects.requireNonNull(denotes, unanswered(fn, "denotes")),
                            Objects.requireNonNull(reachedAs, unanswered(fn, "is reached as")),
                            pos, null),
                    args, origin, pos, region);
        }

        /** Why a pass may not apply a name it has not answered for. */
        private static String unanswered(String fn, String half) {
            return "a pass applying `" + fn + "` says what it means: nothing here " + half
                    + " it, and the spelling would be resolved again wherever this is read";
        }

        /** Whether what this applies is a name. A reader that wants the name itself matches on
         * {@link #function()}, which is where it is. */
        public boolean appliesAName() {
            return function instanceof Var;
        }

        /**
         * The name this applies as the source writes it, or the empty spelling where what it
         * applies is not a name. What a report quotes and underlines.
         *
         * <p><b>Never a lookup key.</b> An import lets a library name be written without its
         * qualifier, so a table keyed by a declaration's name misses on the spelling — silently,
         * because a miss is what a table keyed by names does with one it has not got. Every
         * question of the form "which declaration is this" asks {@link #reaches()}.
         *
         * <p>{@link #appliedAs} answers where a lowering replaced what was written with a binding
         * it introduced: applying something other than a name binds it first, and the binding is
         * named nothing an author could have typed. The two are separate for that reason — this
         * one is read by reports and nothing else.
         */
        public String written() {
            return name().canonical();
        }

        /**
         * The name this applies, with the occurrence of it a report underlines.
         *
         * <p>Where a lowering replaced what was written with a binding it introduced
         * ({@link #appliedAs}), that binding is written nowhere: the characters at {@link #pos()}
         * spell whatever the author applied, which is no longer this.
         */
        public WrittenName name() {
            if (appliedAs != null) {
                return WrittenName.synthetic(appliedAs, pos);
            }
            return function instanceof Var v ? v.written() : WrittenName.synthetic("", pos);
        }

        /**
         * Where a report about what this applies points: the characters the callee was written over.
         *
         * <p>Not {@link #name()}'s. The name is what a report quotes, and where a lowering replaced
         * what was written with a binding it introduced ({@link #appliedAs}) that name is written
         * nowhere — while the characters the binding stands for are still there, being whatever the
         * author applied. Asking the callee gets those; asking the name gets a point at best.
         */
        public Region appliedAt() {
            Region written = function.reportedAt();
            return written != null ? written : name().reportedAt();
        }

        /**
         * The name of the declaration this application reaches, or the empty spelling where it
         * reaches none — what a table keyed by a declaration's name is looked up with.
         *
         * <p>A library name is filed under its qualifier whether or not an import let it be written
         * bare, so that is what it answers; every other name is filed as it is written. The empty
         * answer is not a convention: it is what applying something that is not a name leaves, and
         * no declaration is named the empty spelling.
         *
         * <p>Never {@link #written()}: a spelling a report quotes is not what this application
         * reaches, and a lowering that put one there would otherwise have every table in the
         * compiler looked up with it.
         */
        public String reaches() {
            return function instanceof Var v ? v.reaches() : "";
        }

        /** How this module reaches what the application applies, or null where what it applies is
         * not a name. Settled at resolution and carried, so it says the same thing whichever passes
         * have run. */
        public ReachName reachedAs() {
            return function instanceof Var v ? v.reachedAs() : null;
        }

        /** What the name this applies denotes, or null where what it applies is not a name. */
        public ValueName denotes() {
            return function instanceof Var v ? v.denotes() : null;
        }


        /** The same application, carried into a body by a value that body named. A recursive helper
         * is lowered to a method rather than expanded, so a value reaching one leaves an application
         * where its constructions would otherwise stand, and it is what has to say where it came
         * from. */
        public Apply carriedByValue() {
            return new Apply(function, args, origin.carriedByValue(), appliedAs, pos, region);
        }

        /** The same application over rewritten arguments — a pass that touches only the arguments
         *  says so here rather than listing the slots it is not changing, which is how
         *  {@link #appliedAs} would be dropped by a rewrite that has no opinion about it. */
        public Apply withArgs(List<Expr> args) {
            return new Apply(function, args, origin, appliedAs, pos, region);
        }
    }

    /** {@code origin} is where the comparison was written, which is not always where the fork
     * testing it was: a condition can be an application of a function parameter, and the predicate
     * handed to it is the caller's. Carried so that two predicates written separately stay two lines
     * and one predicate applied twice stays one ({@link CoverageOrigin}). */
    record Binary(BinOp op, Expr left, Expr right, CoverageOrigin origin, SourcePos pos,
                  Region region) implements Expr {}


    enum BinOp { EQ, NE, LT, LE, GT, GE, AND, OR, ADD, SUB, MUL, DIV, CONCAT }

    /**
     * {@code e} with each of its slots replaced by what the operator for that slot answers, its own
     * kind and position kept — or {@code e} itself where every slot answered what it was given, so a
     * walk that only reads allocates nothing.
     *
     * <p>The children of an expression occupy two kinds of slot, and they differ in what may stand
     * there. An expression slot takes any expression — an argument, a field's value, the thing an
     * {@code if} tests. A name slot takes only a name: a construction's spread {@code T { ..base }}
     * copies the fields of what the name stands for, so there is nothing there to evaluate and
     * nothing else that could be written.
     *
     * <p>This is the one place that says which slots a node has. Both {@link #mapChildren} and
     * {@link #forEachChild} are derived from it, so a slot a node gains later is written once and
     * neither walk can be left behind. Being exhaustive over {@code Expr}, a node kind added later
     * stops the build here, which is the one place it has to be accounted for.
     */
    /**
     * {@code e} written over {@code region} instead of whatever it says now — for the one caller
     * that knows a wider stretch of source than the node it is holding.
     *
     * <p>A form the parser reduces away is still characters in the file. {@code (a + 100)} leaves an
     * {@code Ast.Binary} because the parentheses say nothing the tree needs to keep, and they are
     * nine characters the author wrote as that argument all the same. A report that underlined seven
     * of them would be pointing at an expression the reader has to work out is the one it means.
     *
     * <p>The reduction is the frontend's and so is this: nowhere downstream is there anything left
     * saying the parentheses were ever there.
     */
    public static Expr withRegion(Expr e, Region region) {
        return switch (e) {
            case IntLit x -> new IntLit(x.value(), x.pos(), region);
            case DecimalLit x -> new DecimalLit(x.value(), x.pos(), region);
            case StringLit x -> new StringLit(x.value(), x.pos(), region);
            case BoolLit x -> new BoolLit(x.value(), x.pos(), region);
            case Var x -> new Var(x.written(), x.denotes(), x.reachedAs(), region);
            case Unreachable x -> new Unreachable(x.reason(), x.pos(), region);
            case Neg x -> new Neg(x.operand(), x.pos(), region);
            case FieldAccess x -> new FieldAccess(x.target(), x.name(), x.pos(), region);
            case Binary x -> new Binary(x.op(), x.left(), x.right(), x.origin(), x.pos(), region);
            case Apply x -> new Apply(x.function(), x.args(), x.origin(), x.appliedAs(), x.pos(),
                    region);
            case If x -> new If(x.cond(), x.then(), x.els(), x.origin(), x.pos(), region);
            case IfConstructed x ->
                    new IfConstructed(x.construct(), x.binder(), x.then(), x.els(), x.origin(), x.pos(),
                            region);
            case LetIn x -> new LetIn(x.binder(), x.value(), x.declaredType(), x.annotated(),
                    x.opens(), x.body(), x.pos(), region);
            case Expansion x -> new Expansion(x.callee(), x.application(), x.bound(), x.given(),
                    x.declaredReturn(), x.body(), x.pos(), region);
            case Block x -> new Block(x.params(), x.body(), x.pos(), region);
            case ListLit x -> new ListLit(x.elements(), x.pos(), region);
            case ListComp x -> new ListComp(x.element(), x.guards(), x.origin(), x.pos(), region);
            case Tuple x -> new Tuple(x.elements(), x.pos(), region);
            case TupleGet x -> new TupleGet(x.tuple(), x.index(), x.arity(), x.pos(), region);
            case NewData x ->
                    new NewData(x.typeName(), x.inits(), x.spreads(), x.origin(), x.pos(), region);
            case Match x -> new Match(x.scrutinee(), x.cases(), x.origin(), x.pos(), region);
        };
    }

    private static Expr atSlots(Expr e, UnaryOperator<Expr> atExpr, UnaryOperator<Var> atName) {
        return switch (e) {
            case IntLit x -> x;
            case DecimalLit x -> x;
            case StringLit x -> x;
            case BoolLit x -> x;
            case Var x -> x;
            case Unreachable x -> x;
            case Neg n -> {
                Expr operand = atExpr.apply(n.operand());
                yield operand == n.operand() ? n : new Neg(operand, n.pos(), n.region());
            }
            case FieldAccess fa -> {
                Expr target = atExpr.apply(fa.target());
                yield fa.withTarget(target);
            }
            case Binary b -> {
                Expr left = atExpr.apply(b.left());
                Expr right = atExpr.apply(b.right());
                yield left == b.left() && right == b.right() ? b
                        : new Binary(b.op(), left, right, b.origin(), b.pos(), b.region());
            }
            case Apply a -> {
                Expr function = atExpr.apply(a.function());
                List<Expr> args = each(a.args(), atExpr);
                yield function == a.function() && args == a.args() ? a
                        : new Apply(function, args, a.origin(), a.appliedAs(), a.pos(), a.region());
            }
            case If iff -> {
                Expr cond = atExpr.apply(iff.cond());
                Expr then = atExpr.apply(iff.then());
                Expr els = atExpr.apply(iff.els());
                yield cond == iff.cond() && then == iff.then() && els == iff.els() ? iff
                        : new If(cond, then, els, iff.origin(), iff.pos(), iff.region());
            }
            case IfConstructed ic -> {
                Expr construct = atExpr.apply(ic.construct());
                Expr then = atExpr.apply(ic.then());
                List<ElseArm> els = each(ic.els(), arm -> {
                    Expr body = atExpr.apply(arm.body());
                    return body == arm.body() ? arm : arm.with(body);
                });
                yield construct == ic.construct() && then == ic.then() && els == ic.els() ? ic
                        : new IfConstructed(construct, ic.binder(), then, els, ic.origin(), ic.pos(),
                                ic.region());
            }
            case LetIn li -> {
                Expr value = atExpr.apply(li.value());
                Expr body = atExpr.apply(li.body());
                yield value == li.value() && body == li.body() ? li
                        : new LetIn(li.binder(), value, li.declaredType(), li.annotated(),
                                li.opens(), body, li.pos(), li.region());
            }
            // `given` is not a slot. What stands there is caller code that is also inside `body`,
            // wherever the callee applies it, so a walk that took both would read one lambda twice —
            // and rewrite it into two different things. It is read only by whoever asks what the
            // signature said about it.
            case Expansion ex -> {
                List<Bound> bound = each(ex.bound(), b -> {
                    Expr value = atExpr.apply(b.value());
                    return value == b.value() ? b
                            : new Bound(b.binder(), b.declaredType(), value);
                });
                Expr body = atExpr.apply(ex.body());
                yield bound == ex.bound() && body == ex.body() ? ex
                        : new Expansion(ex.callee(), ex.application(), bound, ex.given(),
                                ex.declaredReturn(), body, ex.pos(), ex.region());
            }
            case Block bl -> {
                Expr body = atExpr.apply(bl.body());
                yield body == bl.body() ? bl : new Block(bl.params(), body, bl.pos(), bl.region());
            }
            case ListLit l -> {
                List<Expr> elements = each(l.elements(), atExpr);
                yield elements == l.elements() ? l : new ListLit(elements, l.pos(), l.region());
            }
            case ListComp comp -> {
                Expr element = atExpr.apply(comp.element());
                List<Expr> guards = each(comp.guards(), atExpr);
                yield element == comp.element() && guards == comp.guards() ? comp
                        : new ListComp(element, guards, comp.origin(), comp.pos(), comp.region());
            }
            case Tuple tup -> {
                List<Expr> elements = each(tup.elements(), atExpr);
                yield elements == tup.elements() ? tup : new Tuple(elements, tup.pos(), tup.region());
            }
            case TupleGet tg -> {
                Expr tuple = atExpr.apply(tg.tuple());
                yield tuple == tg.tuple() ? tg
                        : new TupleGet(tuple, tg.index(), tg.arity(), tg.pos(), tg.region());
            }
            case NewData nd -> {
                // the spreads first: `..base` is written before the fields that replace what it
                // brought, and a walk that records the first thing it sees should see them that way
                List<Var> spreads = each(nd.spreads(), atName);
                List<FieldInit> inits = each(nd.inits(), i -> {
                    Expr value = atExpr.apply(i.value());
                    return i.withValue(value);
                });
                yield spreads == nd.spreads() && inits == nd.inits() ? nd
                        : new NewData(nd.typeName(), inits, spreads, nd.origin(), nd.pos(), nd.region());
            }
            case Match m -> {
                Expr scrutinee = atExpr.apply(m.scrutinee());
                List<Case> cases = each(m.cases(), c -> {
                    Expr body = atExpr.apply(c.body());
                    return body == c.body() ? c
                            : new Case(c.caseTypes(), c.binding(), body, c.unwrapAsserts(), c.pos());
                });
                yield scrutinee == m.scrutinee() && cases == m.cases() ? m
                        : new Match(scrutinee, cases, m.origin(), m.pos(), m.region());
            }
        };
    }

    /** {@code xs} with {@code f} applied to each, or {@code xs} itself where none of them changed. */
    private static <T> List<T> each(List<T> xs, UnaryOperator<T> f) {
        List<T> out = null;
        for (int i = 0; i < xs.size(); i++) {
            T before = xs.get(i);
            T after = f.apply(before);
            if (out == null && after != before) {
                out = new ArrayList<>(xs.subList(0, i));
            }
            if (out != null) {
                out.add(after);
            }
        }
        return out == null ? xs : out;
    }

    /**
     * Rebuilds {@code e} with each of its slots replaced by what the operator for that slot answers;
     * a leaf (a literal, a name) is returned unchanged. The single authoritative rewrite over the
     * expression tree, so an AST-to-AST pass (a Lower desugar, an optimization) writes only the cases
     * it rewrites and delegates the rest here, instead of hand-copying every node type.
     *
     * <p>The two operators are the two kinds of slot. {@code onNameSlot} answers a {@link Var}
     * because that is all a spread may hold, so a rewrite cannot put an expression where the language
     * admits only a name; a pass that does have an expression to put there — the inliner — binds it
     * ahead of the construction and spreads the binding. There is no one-operator form: what a
     * rewrite does to a name is a decision, and it is made where the rewrite is written.
     */
    static Expr mapChildren(Expr e, UnaryOperator<Expr> onExprSlot, UnaryOperator<Var> onNameSlot) {
        return atSlots(e, onExprSlot, onNameSlot);
    }

    /**
     * Applies {@code f} to each direct child of {@code e} (a leaf has none) — the read-only
     * counterpart of {@link #mapChildren}. A visiting pass (a checker walk) delegates its default
     * recursion here rather than hand-copying every node type.
     *
     * <p>A name a spread holds is a child like any other, so a pass that asks what an expression
     * names reaches one without knowing that spreads exist.
     */
    public static void forEachChild(Expr e, java.util.function.Consumer<Expr> f) {
        atSlots(e, child -> {
            f.accept(child);
            return child;
        }, child -> {
            f.accept(child);
            return child;
        });
    }

    /** Rewrites each clause's expression, keeping its name. Every stage that rewrites a declaration's
     * invariant goes through here, so no rewrite can drop the name the failure is classified by. */
    public static List<InvariantClause> mapClauses(List<InvariantClause> clauses, UnaryOperator<Expr> f) {
        List<InvariantClause> out = new ArrayList<>();
        for (InvariantClause clause : clauses) {
            out.add(clause.with(f.apply(clause.expr())));
        }
        return out;
    }

    /** Rewrites each departure's body, keeping the clause it answers. */
    public static List<ElseArm> mapArms(List<ElseArm> arms, UnaryOperator<Expr> f) {
        List<ElseArm> out = new ArrayList<>();
        for (ElseArm arm : arms) {
            out.add(arm.with(f.apply(arm.body())));
        }
        return out;
    }
}
