package souther.compiler.ast;

import souther.compiler.diag.SourcePos;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.ConstructionOrigin;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;
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

        /** How the binding was written. A diagnostic quotes this, and a generated local is named
         * after it; nothing decides identity by it. */
        String name();

        /** A binder as the parser read it, before resolution has said which binding it is. */
        static Binder written(String name, SourcePos pos) {
            return new Written(name, pos);
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
        record Written(String name, SourcePos pos) implements Binder {

            @Override
            public String toString() {
                return name;
            }
        }

        /** A binder resolution answered, and the binding it introduces. */
        record Bound(String name, BindingId binding, SourcePos pos) implements Binder {

            public Bound {
                if (binding == null) {
                    throw new IllegalArgumentException("a bound binder is a binding: " + name);
                }
            }

            @Override
            public String toString() {
                return name;
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

        /** A binding nothing else has, under this pass's owner. */
        public Binder binder(String name, SourcePos pos) {
            return new Binder.Bound(name, new BindingId(owner, next++), pos);
        }
    }

    /**
     * A name that denotes a declared type, in both forms it has: {@code written} as the source spelled
     * it — bare {@code 金額}, qualified {@code billing.金額}, or through an import alias — and
     * {@code denotes} as it resolves. Resolution happens once, in {@code Resolve}, before any check
     * runs; every name-bearing position in this tree carries one of these, so no later pass decides
     * for itself what a spelling means or whether a qualified one is allowed here (issue #177).
     *
     * <p>A check reads {@link #denotes()}, which is set on every name the resolve pass let through —
     * a name that denotes nothing is reported there and the compile stops, so nothing downstream sees
     * an unresolved one. {@link #written()} is for a diagnostic that quotes the source, and is not
     * what two names are compared by: a bare and a qualified spelling of one type are one name.
     */
    record Name(String written, TypeName denotes, SourcePos pos) implements Ast {

        /** A name as the parser read it, before the resolve pass has said what it denotes. Only the
         * parser writes one: every other producer knows what it means and says so. */
        public static Name written(String written, SourcePos pos) {
            return new Name(written, null, pos);
        }

        /** A name a pass synthesized, already knowing what it denotes. */
        public static Name resolved(TypeName denotes, SourcePos pos) {
            return new Name(denotes.name(), denotes, pos);
        }

        /** The same name, resolved to what it denotes. */
        public Name denoting(TypeName resolved) {
            return new Name(written, resolved, pos);
        }

        @Override
        public String toString() {
            return written;
        }
    }

    /**
     * A name in the value namespace, in both forms it has: {@code written} as the source spelled it —
     * bare {@code price}, qualified {@code billing.price}, or through an import alias — and
     * {@code denotes} as it resolves. What {@link Name} is for a type.
     *
     * <p>A check reads {@link #denotes()}. A name that denotes nothing was reported where it was
     * written and carries {@link ValueName.Unresolved}, so a reader downstream never has a spelling
     * to match and never repeats the report.
     */
    record ValueRef(String written, ValueName denotes, SourcePos pos) implements Ast {

        /** A name as the parser read it, before resolution has said what it denotes. */
        public static ValueRef written(String written, SourcePos pos) {
            return new ValueRef(written, null, pos);
        }

        /** A name a pass introduced, reading the binding it bound it to — the counterpart of
         * {@link Var#local}. */
        public static ValueRef local(Binder binder, SourcePos pos) {
            return new ValueRef(binder.name(), new ValueName.Local(binder.name(), binder.id()), pos);
        }

        /** The same name, resolved to what it denotes. */
        public ValueRef denoting(ValueName resolved) {
            return new ValueRef(written, resolved, pos);
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
                throw new IllegalStateException("`" + written + "` was never resolved");
            }
            return denotes.name();
        }

        /** Whether this name denotes nothing — reported where it was written. */
        public boolean unresolved() {
            return denotes instanceof ValueName.Unresolved;
        }

        @Override
        public String toString() {
            return written;
        }
    }

    /**
     * A whole source file: its public surface, imports, and definitions.
     *
     * <p>{@code exposedOutputs} maps an exposed composition behavior's name to the output signature
     * written in the {@code exposing} list ({@code exposing ( name : A | B )}, spec 14.5). An exposed
     * {@code >->} composition must have one, checked to match its inferred output (ADR-0024); other
     * exposed names carry no signature (their type is at the definition).
     */
    record Module(String name,
                  List<String> exposing,
                  Map<String, RetType> exposedOutputs,
                  List<Import> imports,
                  List<Def> defs,
                  List<BehaviorDef> behaviors,
                  List<FnDef> fns,
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

    /** {@code import <module> ( name, ... )} — an explicit, non-wildcard import (spec 4). */
    /**
     * {@code import a.b as B ( X, Y )}. {@code names} are the names this import brings into scope
     * bare; {@code alias} is the qualifier the module is read under here, or null. Both parts are
     * optional: a type is reachable qualified whether or not it was imported (spec 4), so an import
     * with neither is just the dependency written down.
     */
    record Import(String module, String alias, List<String> names, SourcePos pos) implements Ast {}

    /**
     * A behavior definition — a specification, not an implementation (spec 12, 21.1). It is either
     * a {@link SpecBehavior} (an input/output signature, with the body left to a matching
     * {@link FnDef} or to Java injection) or a {@link PipeBehavior} (a {@code >->} composition, which
     * is itself the implementation).
     */
    sealed interface BehaviorDef extends Ast permits SpecBehavior, PipeBehavior {
        String name();
    }

    /**
     * {@code behavior name = (p1: T1, ...) -> R constructs A, B depends on C, D} — a signature with
     * no body (spec 12.1). A same-named {@link FnDef} is its implementation (13.1); with none, and
     * not a pipeline, it is a Java-injected behavior (13.2).
     *
     * <p>{@code dependsOn} lists the implementation-less behaviors the {@code fn} calls; they become
     * the {@code fn}'s trailing arguments and the injected fields of the generated class (12.6).
     */
    record SpecBehavior(String name,
                        List<Param> params,
                        RetType ret,
                        List<Name> constructs,
                        List<ValueRef> dependsOn,
                        SourcePos pos) implements BehaviorDef {}

    /** A behavior parameter. Its type may be an anonymous union of cases (spec 12.2). */
    record Param(String name, RetType type, SourcePos pos) implements Ast {}

    /**
     * {@code behavior name = f >-> g >-> ... [-> A | B]} — a composition (spec 14.1). {@code declaredOut}
     * is the optional trailing output declaration (14.5): null when absent (output is inferred), else
     * the declared cases, which must match the inferred output exactly (E1604).
     */
    record PipeBehavior(String name, List<ValueRef> stages, RetType declaredOut, SourcePos pos)
            implements BehaviorDef {}

    /**
     * {@code fn name (a1, ...) = body} — a behavior's implementation (spec 13.1). If a same-named
     * {@link SpecBehavior} exists, the parameter types come from it and the author writes none
     * ({@link FnParam#type()} is null, or read off a pattern; {@link FnParam#typeFromPattern()});
     * otherwise it is a helper {@code fn} that writes its own parameter types.
     *
     * <p>{@code body} is a single expression. The surface forms {@code let} and {@code guard} are
     * desugared by the parser into {@link LetIn} and {@link If} (spec 16.4), so every later stage
     * sees one expression tree and has exactly one place where a value can be constructed.
     */
    /**
     * A {@code let} definition. A behavior fn or a helper carries a {@code body} and no
     * {@code declaredReturn}/{@code intrinsicKey}. A core intrinsic (spec §primitives) instead
     * declares its return type and names a primitive: {@code let trim (s: String): String =
     * intrinsic "string.trim"} — its {@code body} is null, {@code declaredReturn} its result type,
     * and {@code intrinsicKey} the backend key. Intrinsics are written only in the {@code souther}
     * namespace. {@code partial} marks a helper that opts out of the totality check (spec
     * §fn-declaration): a recursive helper is checked for structural recursion unless it is
     * {@code partial}.
     */
    record FnDef(String name, List<FnParam> params, RetType declaredReturn, String intrinsicKey,
                 Expr body, boolean partial, SourcePos pos) implements Ast {
        /** A fn with no {@code partial} marker (the common case; totality-checked if recursive). */
        public FnDef(String name, List<FnParam> params, RetType declaredReturn, String intrinsicKey,
                     Expr body, SourcePos pos) {
            this(name, params, declaredReturn, intrinsicKey, body, false, pos);
        }

        public boolean isIntrinsic() {
            return intrinsicKey != null;
        }
    }

    /** A {@code fn} parameter: a name, and a type only when the {@code fn} is a helper (spec 13.1).
     * A helper's parameter type may be a function type {@link FnType}; a behavior fn's parameter
     * carries no type ({@code type} is null). {@code typeFromPattern} marks a type read off a
     * constructor pattern in parameter position rather than written beside the name — a behavior's
     * implementation may write the pattern, and its type still comes from the behavior. */
    record FnParam(Binder binder, RetType type, boolean typeFromPattern) implements Ast {
        /** A parameter whose type, if any, the author wrote (the common case). */
        public FnParam(Binder binder, RetType type) {
            this(binder, type, false);
        }

        /** A parameter as the parser read it. */
        public FnParam(String name, RetType type, SourcePos pos) {
            this(Binder.written(name, pos), type, false);
        }

        public String name() {
            return binder.name();
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

    /** A written type: one term, or the unmarked sum of several (spec 12.2). */
    record RetType(List<TypeTerm> cases, SourcePos pos) implements Ast {

        /** The function type this stands for, or null when it is not a lone function type. A sum of
         * a function with anything else is not one, and has no case to be told apart by. */
        public FnType asFn() {
            return cases.size() == 1 && cases.get(0) instanceof FnType fn ? fn : null;
        }
    }

    /** A top-level data definition: product, sum, or unit. */
    sealed interface Def extends Ast permits Data, SumData, UnitData {
        String name();

        SourcePos pos();
    }

    /**
     * A product data definition: included data (flattened) plus its own fields.
     *
     * <p>{@code newtype} marks the explicit newtype form {@code data X = Y} (spec 8.7): a single
     * implicit field named {@code value} of type {@code Y}, encoded as bare {@code Y} instead of an
     * object. Everything else (construction {@code X { value: v }}, access {@code x.value},
     * invariant on {@code value}) is the same as a one-field product; only the external
     * representation differs.
     */
    record Data(String name,
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
    record SumData(String name,
                   List<Name> cases,
                   Optional<Discriminate> decoder,
                   Optional<SumEncoder> encoder,
                   SourcePos pos) implements Def {}

    /** {@code encoder discriminate on "key" { Case -> "tag" ... }} — the inverse of discriminate. */
    record SumEncoder(String key, List<EncVariant> variants, SourcePos pos) implements Ast {}

    record EncVariant(Name caseType, String tag, SourcePos pos) implements Ast {}

    /** A unit data definition {@code data U} with no fields. */
    record UnitData(String name, SourcePos pos) implements Def {}

    /** {@code decoder from Object discriminate on "key" { "tag" -> Case.decoder ... }} */
    record Discriminate(String key, List<Variant> variants, SourcePos pos) implements Ast {}

    record Variant(String tag, Name caseType, SourcePos pos) implements Ast {}

    /** A field: a role name and its type. */
    record Field(String name, TypeTerm type, SourcePos pos) implements Ast {}

    /**
     * A named type reference, optionally with one type argument (e.g. {@code List<T>}). When
     * {@code name} is null and {@code tupleElems} is non-null the ref is a tuple type
     * {@code (A, B, ...)} (ADR-0036), written only in a helper/stdlib signature. A {@code Map<K, V>}
     * reuses {@code tupleElems} to carry its key type (a single element) while {@code name} is
     * {@code "Map"} and {@code arg} is the value type (ADR-0040).
     *
     * <p>{@code denotes} is the type the reference stands for, decided once by {@code Resolve}
     * (issue #177). Every reference the pass let through carries one, so nothing downstream resolves
     * a written type a second time — nor has to know which module the reference was written in, which
     * is what a second resolution needed to get right.
     */
    record TypeRef(String name, TypeTerm arg, List<TypeTerm> tupleElems, Type denotes, SourcePos pos)
            implements TypeTerm {
        /** A reference as the parser read it, before the resolve pass has said what it denotes. */
        public TypeRef(String name, TypeTerm arg, List<TypeTerm> tupleElems, SourcePos pos) {
            this(name, arg, tupleElems, null, pos);
        }

        /** An ordinary (non-tuple) reference. */
        public TypeRef(String name, TypeTerm arg, SourcePos pos) {
            this(name, arg, null, null, pos);
        }

        /** The same reference, resolved. */
        public TypeRef denoting(Type type) {
            return new TypeRef(name, arg, tupleElems, type, pos);
        }

        /**
         * A reference nobody wrote: it carries what it denotes and no surface text. A helper
         * parameter whose type its body settles is written back as one (issue #178) — the type is
         * decided, and there is no source it stands for. Everything downstream of {@code Resolve}
         * reads {@link #denotes()}, so a reference with a decided type is as good as a written one.
         */
        public static TypeRef of(Type type, SourcePos pos) {
            return new TypeRef(null, null, null, type, pos);
        }

        /** A tuple type is the nameless form; a named ref that also carries {@code tupleElems}
         *  (a {@code Map} carrying its key) is not a tuple. */
        public boolean isTuple() {
            return name == null && tupleElems != null;
        }
    }

    /** The kind of primitive Raw a single-value decoder reads / an encoder writes. */
    enum RawKind { TEXT, INT, BOOL, DECIMAL, DATE, DATETIME }

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
     * A newtype {@code data X = Y} over a non-primitive {@code Y} (spec 8.7): the whole input is
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

    /** {@code name <- field("key", <decRef>)} inside an object decoder. */
    record Bind(Binder binder, String key, DecRef ref, SourcePos pos) implements Ast {

        public String name() {
            return binder.name();
        }
    }

    /** The decoder referenced by a bind: a primitive, another data's {@code .decoder}, or a list. */
    sealed interface DecRef extends Ast
            permits PrimDecRef, DataDecRef, ListDecRef, SetDecRef, OptionDecRef, MapDecRef {}

    record PrimDecRef(PrimKind kind, SourcePos pos) implements DecRef {}

    record DataDecRef(Name typeName, SourcePos pos) implements DecRef {}

    /** {@code list(<elementDecRef>)} */
    record ListDecRef(DecRef element, SourcePos pos) implements DecRef {}

    /** {@code set(<elementDecRef>)} — a list decoder deduplicated into a Set on decode (ADR-0009). */
    record SetDecRef(DecRef element, SourcePos pos) implements DecRef {}

    /** An optional field decoder: absent/null becomes {@code None}, present decodes {@code element}. */
    record OptionDecRef(DecRef element, SourcePos pos) implements DecRef {}

    /** A {@code Map<K, T>} decoder: each object value is decoded with {@code value}, and each of the
     * object's string keys with {@code key} — a {@code PrimDecRef} of {@code STRING} (the key passes
     * through), of {@code DATE}/{@code DATETIME} (parsed from its ISO form), or a {@code DataDecRef}
     * naming the String-backed newtype the keys are constructed into. */
    record MapDecRef(DecRef value, DecRef key, SourcePos pos) implements DecRef {}

    /** A primitive field decoder kind. */
    enum PrimKind { STRING, INT, BOOL, DECIMAL, DATE, DATETIME }

    /** A statement in a single-value decoder body. */
    sealed interface DecStmt extends Ast permits Let {}

    record Let(Binder binder, Expr value, SourcePos pos) implements DecStmt {

        public String name() {
            return binder.name();
        }
    }

    /** A typed record literal {@code TypeName { ..src, field: expr, ... }} — a construction. */
    record Construct(Name typeName, List<FieldInit> inits, List<String> spreads, SourcePos pos)
            implements Ast {}

    /** One {@code field: expr} (or shorthand {@code field}) inside a record literal. */
    record FieldInit(String name, Expr value, SourcePos pos) implements Ast {}

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
     * to its bare string via {@code key} — a {@code PrimEnc} of {@code STRING} (already a string),
     * of {@code DATE}/{@code DATETIME} (its ISO form), or a {@code DataEnc} naming the String-backed
     * newtype whose wrapped value is rendered. */
    record MapEnc(Expr source, EncElem elem, EncElem key, SourcePos pos) implements RawExpr {}

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
    sealed interface EncElem extends Ast permits PrimEnc, DataEnc, ListElemEnc, SetElemEnc, MapElemEnc {}

    record PrimEnc(PrimKind kind, SourcePos pos) implements EncElem {}

    record DataEnc(Name typeName, SourcePos pos) implements EncElem {}

    /** A {@code List<T>} element, each {@code T} encoded by {@code elem}. */
    record ListElemEnc(EncElem elem, SourcePos pos) implements EncElem {}

    /** A {@code Set<T>} element: listed, then each element encoded by {@code elem}, as {@link SetEnc}
     * does for a field. */
    record SetElemEnc(EncElem elem, SourcePos pos) implements EncElem {}

    /** A {@code Map<K, V>} element, each value encoded by {@code value} and each key by {@code key},
     * as {@link MapEnc} does for a field. */
    record MapElemEnc(EncElem value, EncElem key, SourcePos pos) implements EncElem {}

    record RawEntry(String key, RawExpr value, SourcePos pos) implements Ast {}

    // --- expressions ---

    sealed interface Expr extends Ast
            permits IntLit, DecimalLit, StringLit, BoolLit, Var, FieldAccess, Apply, Binary, Neg,
                    NewData, Match, If, IfConstructed, ListLit, ListComp, LetIn, Block, Tuple,
                    TupleGet, Unreachable {}

    /**
     * {@code unreachable "reason"} — the point the model says cannot arise (spec 16.3).
     *
     * <p>It answers no value, so it has no type of its own to check against the position it is
     * written in: it types at {@code Never} and fits whatever is expected. The reason is a literal
     * rather than an expression so that the compiler and a reader both have it without running the
     * model; at run time it is the message the abort carries.
     */
    record Unreachable(String reason, SourcePos pos) implements Expr {}

    /**
     * {@code x -> expr}, or {@code (acc, x) -> expr} — a block (spec 12.5).
     *
     * <p>Second-class: it may only be an argument, never a value that is returned, stored in a
     * field, or bound by {@code let}. The parser only accepts one in an argument position, and
     * because it cannot escape, the backend inlines it rather than building a closure.
     */
    record Block(List<Binder> params, Expr body, SourcePos pos) implements Expr {

        /** A block as the parser read it. */
        public static Block written(List<String> params, Expr body, SourcePos pos) {
            List<Binder> binders = new ArrayList<>();
            for (String p : params) {
                binders.add(Binder.written(p, pos));
            }
            return new Block(binders, body, pos);
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
     * (spec 16.1). Nesting the rest of the body inside keeps {@code value} from being evaluated
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
                 Expr body, SourcePos pos) implements Expr {
        /** An ordinary {@code let x = e}: the bound name takes {@code e}'s inferred type. */
        public LetIn(Binder binder, Expr value, Expr body, SourcePos pos) {
            this(binder, value, null, false, null, body, pos);
        }

        /** The same, as the parser read it. */
        public LetIn(String name, Expr value, Expr body, SourcePos pos) {
            this(Binder.written(name, pos), value, null, false, null, body, pos);
        }

        /** A binding carrying an inlined helper parameter's declared type. */
        public LetIn(Binder binder, Expr value, RetType declaredType, Expr body, SourcePos pos) {
            this(binder, value, declaredType, false, null, body, pos);
        }

        /** {@code let x: T = value} — a binding the source annotated. */
        public static LetIn annotated(String name, Expr value, RetType type, Expr body, SourcePos pos) {
            return new LetIn(Binder.written(name, pos), value, type, true, null, body, pos);
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
        public static LetIn opening(String name, Expr value, Name opens, Expr body, SourcePos pos) {
            return new LetIn(Binder.written(name, pos), value, null, false, opens, body, pos);
        }

        /** The type the source wrote on this binding, or null when it wrote none. An annotation is an
         * ordinary type (a function type belongs only in a helper's parameter), so this is the one
         * place that narrows {@code declaredType}, and a carrier from inlining never reads as one. */
        public RetType annotation() {
            return annotated && declaredType instanceof RetType rt ? rt : null;
        }
    }

    /** A list literal {@code [e1, e2, ...]} (one or more elements of the same type). */
    record ListLit(List<Expr> elements, SourcePos pos) implements Expr {}

    /** A guard-only comprehension {@code [element | guard, ...]}: the element is included when
     * every guard holds, giving a 0-or-1 element list (spec 18.4, conditional accumulation). */
    record ListComp(Expr element, List<Expr> guards, SourcePos pos) implements Expr {}

    /** A tuple {@code (e1, e2, ...)} of two or more values (ADR-0036), an expression-level value
     * that never crosses the data/behavior boundary. Opened with a {@code let (x, y) = t} destructure. */
    record Tuple(List<Expr> elements, SourcePos pos) implements Expr {}

    /** Reads the {@code index}-th element of a tuple; what a {@code let (x, y) = t} destructure lowers
     * a field read to. Not written in source — the parser produces it from a tuple pattern. {@code arity}
     * is the pattern's name count, so the checker rejects a tuple of a different size (ADR-0036). */
    record TupleGet(Expr tuple, int index, int arity, SourcePos pos) implements Expr {}

    /** {@code if cond then a else b} — both branches must have the same type (spec 16.2). */
    record If(Expr cond, Expr then, Expr els, SourcePos pos) implements Expr {}

    /**
     * {@code if T(v) as x then a else b} — an attempted construction, and what
     * {@code guard T(v) as x else b} desugars to. {@code construct}'s invariant decides the branch:
     * holding, the value is built and {@code binder} names it in {@code then}; failing, {@code els} is
     * taken and no value is built. The binder is scoped to {@code then} alone, which is why this is a
     * node of its own rather than a condition {@code If} would have to introspect — a plain
     * {@code If}'s condition never binds.
     *
     * <p>A construction here does not abort, so it is exempt from the possible-violation warning
     * (spec 7.6); a violation the compiler *decides* is still reported, because then no branch was
     * ever in question.
     *
     * <p>{@code construct} is an {@link Expr} rather than a {@link NewData} because the newtype
     * spelling {@code T(v)} is a {@link Call} until {@link souther.compiler.check.NewtypeDesugar}
     * rewrites it — the same reason nothing else in the AST can name a construction by type either.
     * That it is one, and that its type carries an invariant to attempt, are checked once the names
     * are resolved.
     */
    record IfConstructed(Expr construct, Binder binder, Expr then, List<ElseArm> els, SourcePos pos)
            implements Expr {

        /** The attempt whose failure is not told apart: one arm, naming no clause. */
        public IfConstructed(Expr construct, Binder binder, Expr then, Expr els, SourcePos pos) {
            this(construct, binder, then, List.of(ElseArm.any(els)), pos);
        }

        /** The same, as the parser read it. */
        public IfConstructed(Expr construct, String binder, Expr then, Expr els, SourcePos pos) {
            this(construct, Binder.written(binder, pos), then, List.of(ElseArm.any(els)), pos);
        }

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

    /** {@code match scrutinee { case Case as x -> body ... }} over a sum type. */
    record Match(Expr scrutinee, List<Case> cases, SourcePos pos) implements Expr {}

    /**
     * One {@code match} case: {@code case A | B ... [as x] -> body} (spec 16.3). {@code caseTypes}
     * holds one case name, or several joined by {@code |} (an or-pattern, spec 16.3). With one case,
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

        /** An arm as the parser read it; {@code binding} is null where the arm binds nothing. */
        public static Case written(List<Name> caseTypes, String binding, Expr body,
                                   List<Name> unwrapAsserts, SourcePos pos) {
            return new Case(caseTypes, binding == null ? null : Binder.written(binding, pos), body,
                    unwrapAsserts, pos);
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
    record NewData(Name typeName, List<FieldInit> inits, List<ValueRef> spreads,
                   ConstructionOrigin origin, SourcePos pos) implements Expr {

        /** The same construction, carried into a reader by {@code module}'s published body. */
        public NewData publishedBy(String module) {
            return new NewData(typeName, inits, spreads, origin.publishedIn(module), pos);
        }

        /** The same construction, carried into a body by a value that body named. */
        public NewData carriedByValue() {
            return new NewData(typeName, inits, spreads, origin.carriedByValue(), pos);
        }
    }

    record IntLit(long value, SourcePos pos) implements Expr {}

    record DecimalLit(java.math.BigDecimal value, SourcePos pos) implements Expr {}

    /** Unary minus {@code -operand} on an Int or Decimal (spec 18.1). */
    record Neg(Expr operand, SourcePos pos) implements Expr {}

    record StringLit(String value, SourcePos pos) implements Expr {}

    record BoolLit(boolean value, SourcePos pos) implements Expr {}

    /**
     * A name used as a value. {@code denotes} is what it names, answered once during resolution; a
     * reader asks it rather than deciding for itself whether the spelling is a local, a unit data or
     * something the language provides.
     */
    record Var(String name, ValueName denotes, SourcePos pos) implements Expr {

        /** A name as the parser read it, before resolution has said what it denotes. */
        public Var(String name, SourcePos pos) {
            this(name, null, pos);
        }

        /**
         * A read of something bound in the body, as a pass that put the binding there writes it.
         *
         * <p>A pass that runs after resolution says what it means rather than leaving a spelling for
         * a reader to work out, so it is given the binder it is reading and answers with that
         * binding. There is no way to write one of these without having the binding in hand.
         */
        public static Var local(Binder binder, SourcePos pos) {
            return new Var(binder.name(), new ValueName.Local(binder.name(), binder.id()), pos);
        }

        public Var denoting(ValueName resolved) {
            return new Var(name, resolved, pos);
        }
    }

    record FieldAccess(Expr target, String field, SourcePos pos) implements Expr {}

    /**
     * A function applied to arguments. {@code function} is the thing being applied, and it is an
     * expression like any other: what is applied is what it answers, not how the application was
     * written.
     *
     * <p>Applying a name is the common case and has its own constructors and readers below. A name
     * carries what it denotes — a helper, a library function, an injected behavior, a function-typed
     * binding, or the type a newtype construction wraps — answered once during resolution.
     */
    record Apply(Expr function, List<Expr> args, ConstructionOrigin origin, SourcePos pos)
            implements Expr {

        /** Applying a name, as the parser read it, before resolution has said what the name denotes. */
        public Apply(String fn, List<Expr> args, SourcePos pos) {
            this(new Var(fn, pos), args, ConstructionOrigin.own(), pos);
        }

        /** Applying a name a pass already knows the meaning of. */
        public Apply(String fn, ValueName denotes, List<Expr> args, ConstructionOrigin origin,
                     SourcePos pos) {
            this(new Var(fn, denotes, pos), args, origin, pos);
        }

        /**
         * The name this applies as it was written, or the empty spelling where what it applies is
         * not a name.
         *
         * <p>A reader keyed by name is asking which declaration this reaches, and an application of
         * something other than a name reaches none. No name is empty, so the empty spelling is that
         * answer wherever such a reader looks — a table miss, a comparison that fails.
         */
        public String fn() {
            return function instanceof Var v ? v.name() : "";
        }

        /** Whether what this applies is a name, which is what the readers keyed by one are asking. */
        public boolean appliesAName() {
            return function instanceof Var;
        }

        /** What the name this applies denotes, or null where what it applies is not a name. */
        public ValueName denotes() {
            return function instanceof Var v ? v.denotes() : null;
        }

        public Apply denoting(ValueName resolved) {
            return new Apply(((Var) function).denoting(resolved), args, origin, pos);
        }

        /** The same application, carried into a body by a value that body named. A recursive helper
         * is lowered to a method rather than expanded, so a value reaching one leaves an application
         * where its constructions would otherwise stand, and it is what has to say where it came
         * from. */
        public Apply carriedByValue() {
            return new Apply(function, args, origin.carriedByValue(), pos);
        }
    }

    record Binary(BinOp op, Expr left, Expr right, SourcePos pos) implements Expr {}


    enum BinOp { EQ, NE, LT, LE, GT, GE, AND, OR, ADD, SUB, MUL, DIV, CONCAT }

    /**
     * Rebuilds {@code e} with each direct child expression replaced by {@code f} applied to it; a
     * leaf (a literal or a variable) is returned unchanged. The single authoritative walk over the
     * expression tree, so an AST-to-AST pass (a Lower desugar, an optimization) writes only the
     * cases it rewrites and delegates the rest here, instead of hand-copying every node type.
     */
    static Expr mapChildren(Expr e, UnaryOperator<Expr> f) {
        return switch (e) {
            case IntLit x -> x;
            case DecimalLit x -> x;
            case StringLit x -> x;
            case BoolLit x -> x;
            case Var x -> x;
            case Unreachable x -> x;
            case Neg n -> new Neg(f.apply(n.operand()), n.pos());
            case FieldAccess fa -> new FieldAccess(f.apply(fa.target()), fa.field(), fa.pos());
            case Binary b -> new Binary(b.op(), f.apply(b.left()), f.apply(b.right()), b.pos());
            case Apply a -> new Apply(f.apply(a.function()), mapExprs(a.args(), f), a.origin(), a.pos());
            case If iff -> new If(f.apply(iff.cond()), f.apply(iff.then()), f.apply(iff.els()), iff.pos());
            case IfConstructed ic -> new IfConstructed(f.apply(ic.construct()), ic.binder(),
                    f.apply(ic.then()), mapArms(ic.els(), f), ic.pos());
            case LetIn li -> new LetIn(li.binder(), f.apply(li.value()), li.declaredType(), li.annotated(),
                    li.opens(), f.apply(li.body()), li.pos());
            case Block bl -> new Block(bl.params(), f.apply(bl.body()), bl.pos());
            case ListLit l -> new ListLit(mapExprs(l.elements(), f), l.pos());
            case ListComp comp -> new ListComp(f.apply(comp.element()), mapExprs(comp.guards(), f), comp.pos());
            case Tuple tup -> new Tuple(mapExprs(tup.elements(), f), tup.pos());
            case TupleGet tg -> new TupleGet(f.apply(tg.tuple()), tg.index(), tg.arity(), tg.pos());
            case NewData nd -> {
                List<FieldInit> inits = new ArrayList<>();
                for (FieldInit i : nd.inits()) {
                    inits.add(new FieldInit(i.name(), f.apply(i.value()), i.pos()));
                }
                yield new NewData(nd.typeName(), inits, nd.spreads(), nd.origin(), nd.pos());
            }
            case Match m -> {
                List<Case> cases = new ArrayList<>();
                for (Case c : m.cases()) {
                    cases.add(new Case(c.caseTypes(), c.binding(), f.apply(c.body()), c.unwrapAsserts(), c.pos()));
                }
                yield new Match(f.apply(m.scrutinee()), cases, m.pos());
            }
        };
    }

    /**
     * Applies {@code f} to each direct child expression of {@code e} (a leaf has none) — the read-only
     * counterpart of {@link #mapChildren}. A visiting pass (a checker walk) delegates its default
     * recursion here rather than hand-copying every node type; being exhaustive over {@code Expr}, a
     * new node kind forces every such walk to acknowledge it.
     */
    public static void forEachChild(Expr e, java.util.function.Consumer<Expr> f) {
        switch (e) {
            case IntLit _ -> { }
            case DecimalLit _ -> { }
            case StringLit _ -> { }
            case BoolLit _ -> { }
            case Var _ -> { }
            case Unreachable _ -> { }
            case Neg n -> f.accept(n.operand());
            case FieldAccess fa -> f.accept(fa.target());
            case Binary b -> {
                f.accept(b.left());
                f.accept(b.right());
            }
            case Apply a -> {
                f.accept(a.function());
                a.args().forEach(f);
            }
            case If iff -> {
                f.accept(iff.cond());
                f.accept(iff.then());
                f.accept(iff.els());
            }
            case IfConstructed ic -> {
                f.accept(ic.construct());
                f.accept(ic.then());
                ic.els().forEach(arm -> f.accept(arm.body()));
            }
            case LetIn li -> {
                f.accept(li.value());
                f.accept(li.body());
            }
            case Block bl -> f.accept(bl.body());
            case ListLit l -> l.elements().forEach(f);
            case ListComp comp -> {
                f.accept(comp.element());
                comp.guards().forEach(f);
            }
            case Tuple tup -> tup.elements().forEach(f);
            case TupleGet tg -> f.accept(tg.tuple());
            case NewData nd -> nd.inits().forEach(i -> f.accept(i.value()));
            case Match m -> {
                f.accept(m.scrutinee());
                m.cases().forEach(c -> f.accept(c.body()));
            }
        }
    }

    private static List<Expr> mapExprs(List<Expr> es, UnaryOperator<Expr> f) {
        List<Expr> out = new ArrayList<>();
        for (Expr e : es) {
            out.add(f.apply(e));
        }
        return out;
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
