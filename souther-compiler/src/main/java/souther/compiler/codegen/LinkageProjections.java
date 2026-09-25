package souther.compiler.codegen;

import souther.compiler.ast.Hir;
import souther.compiler.check.AtomSpace;
import souther.compiler.check.BehaviorImplementation;
import souther.compiler.check.DerivedSymbols;
import souther.compiler.check.PublishedDeclarations;
import souther.compiler.check.ReadableFields;
import souther.compiler.check.Shape;
import souther.compiler.check.Sig;
import souther.compiler.check.TypeOps;
import souther.compiler.check.TypeView;
import souther.compiler.jvm.GeneratedClass;
import souther.compiler.jvm.LinkageProjection;
import souther.compiler.jvm.LinkageTarget;
import souther.compiler.jvm.SoutherJvmAbi;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;

import java.lang.constant.ClassDesc;
import java.lang.constant.MethodTypeDesc;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.SortedMap;
import java.util.TreeMap;

import static souther.compiler.codegen.Descriptors.CD_Behavior;
import static souther.compiler.codegen.Descriptors.MTD_apply;

/**
 * What each declaration of one module offers another module's classes: its projection, made out of
 * what the declaration settled by the rules the emitter emits by.
 *
 * <p>The only place a projection is made. What a module provides is what this answers for it, and a
 * class elsewhere links by what it provides; the module's own classes are emitted by the same rules
 * ({@link BehaviorAbi}, {@link JvmTypes}), so what they declare is what this says they declare.
 *
 * <p>What a projection reads of another module's declarations goes through {@code foreign} and the
 * doors {@code symbols} and {@code published} were built reading into, so what it read is what the
 * module records it was built against. A behavior held by a behavior of this module is held as its
 * own number of inputs has it, and for one declared elsewhere that is a fact of the module that
 * declares it.
 */
public final class LinkageProjections {

    private LinkageProjections() {}

    /**
     * What a module's declarations settled, as a projection is made from them.
     *
     * @param module          the module
     * @param exposing        the names its {@code exposing} line lists, empty where it writes none —
     *                        which exposes everything
     * @param declarations    its declared types, in the order it writes them
     * @param signatures      what each of its behaviors takes and answers, by the behavior
     * @param implementations where each of its behaviors gets its body
     * @param requirements    what each behavior with an implementation is handed, in order
     * @param values          what each value it publishes answers, by the value
     * @param symbols         its declarations, reading into what records another module's
     * @param published       what declarations say, reading into the same
     */
    public record Settled(String module, List<String> exposing, List<TypeKey> declarations,
                          Map<String, Sig> signatures,
                          Map<String, BehaviorImplementation> implementations,
                          Map<String, List<ValueName.Behavior>> requirements,
                          Map<String, Type> values, DerivedSymbols symbols,
                          PublishedDeclarations published) {

        public Settled {
            if (symbols == null || published == null) {
                throw new IllegalArgumentException("a projection reads what each declaration it"
                        + " rests on says, so it is handed somewhere to read every one of them");
            }
            exposing = List.copyOf(exposing);
            declarations = List.copyOf(declarations);
        }

        boolean exposes(String name) {
            return exposing.isEmpty() || exposing.contains(name);
        }
    }

    /**
     * The projection of every declaration {@code settled} holds, by the declaration.
     *
     * @param foreign where a behavior another module declares is read, recording that it was
     */
    public static SortedMap<LinkageTarget, LinkageProjection> of(Settled settled,
                                                                 LinkageReader foreign) {
        SortedMap<LinkageTarget, LinkageProjection> out = new TreeMap<>();
        for (TypeKey declaration : settled.declarations()) {
            LinkageProjection.Data data = data(settled, declaration, foreign);
            out.put(data.target(), data);
        }
        settled.signatures().forEach((name, sig) -> {
            LinkageProjection.Behavior behavior = behavior(settled, name, sig, foreign);
            out.put(behavior.target(), behavior);
        });
        settled.values().forEach((name, answers) -> {
            ValueName.Helper value = new ValueName.Helper(settled.module(), name);
            LinkageProjection.Value projection = new LinkageProjection.Value(value,
                    LinkageProjection.Invocation.of(LinkageProjection.Opcode.STATIC,
                            classOf(new GeneratedClass.Values(settled.module()), foreign), name,
                            MethodTypeDesc.of(Descriptors.CD_Object)),
                    answers);
            out.put(projection.target(), projection);
        });
        return out;
    }

    private static LinkageProjection.Behavior behavior(Settled settled, String name, Sig sig,
                                                       LinkageReader foreign) {
        ValueName.Behavior behavior = new ValueName.Behavior(settled.module(), name);
        BehaviorImplementation state = settled.implementations().get(name);
        if (state == null) {
            throw new IllegalStateException("`" + behavior + "` has a signature and no word on"
                    + " where its body comes from");
        }
        LinkageProjection.Realization realization = switch (state) {
            case IMPLEMENTED -> LinkageProjection.Realization.IMPLEMENTED;
            case UNIMPLEMENTED -> LinkageProjection.Realization.UNWRITTEN;
            case INJECTION_TARGET -> LinkageProjection.Realization.SUPPLIED_BY_JAVA;
        };
        List<Type> takes = sig.inputTypes();
        Type answers = sig.outputType();
        ClassDesc own = classOf(new GeneratedClass.BehaviorInterface(settled.module(), name),
                foreign);
        ClassDesc resultUnion = classOf(new GeneratedClass.BehaviorResult(settled.module(), name),
                foreign);
        LinkageProjection.Invocation apply = takes.size() == 1
                ? LinkageProjection.Invocation.of(LinkageProjection.Opcode.INTERFACE, CD_Behavior,
                        "apply", MTD_apply)
                : LinkageProjection.Invocation.of(
                        realization == LinkageProjection.Realization.SUPPLIED_BY_JAVA
                                ? LinkageProjection.Opcode.VIRTUAL
                                : LinkageProjection.Opcode.INTERFACE, own, "apply",
                        BehaviorAbi.typedApply(takes, answers, resultUnion,
                                t -> typeClass(t, foreign)));
        Optional<LinkageProjection.Construction> construction = Optional.empty();
        if (realization == LinkageProjection.Realization.IMPLEMENTED) {
            List<ValueName.Behavior> dependencies = settled.requirements().get(name);
            if (dependencies == null) {
                throw new IllegalStateException("`" + behavior + "` is built and has no"
                        + " requirement set");
            }
            List<ClassDesc> held = new ArrayList<>();
            for (ValueName.Behavior dependency : dependencies) {
                held.add(heldAs(settled, dependency, foreign));
            }
            ClassDesc implementation = classOf(new GeneratedClass.BehaviorImpl(settled.module(),
                    name), foreign);
            construction = Optional.of(new LinkageProjection.Construction(
                    implementation.descriptorString(), dependencies,
                    BehaviorAbi.constructor(held).descriptorString(),
                    LinkageProjection.Invocation.of(LinkageProjection.Opcode.VIRTUAL,
                            implementation, "apply",
                            BehaviorAbi.erasedApply(takes.size()))));
        }
        return new LinkageProjection.Behavior(behavior, realization, settled.exposes(name), takes,
                answers, BehaviorAbi.heldAs(behavior, takes).descriptorString(), apply,
                construction, answeredThrough(settled, answers, foreign));
    }

    /**
     * What a behavior of this module holds {@code dependency} as: by its own signature where this
     * module declares it, and as its projection says where another module does.
     */
    private static ClassDesc heldAs(Settled settled, ValueName.Behavior dependency,
                                    LinkageReader foreign) {
        if (!dependency.module().equals(settled.module())) {
            return foreign.behavior(dependency).heldAsClass();
        }
        Sig sig = settled.signatures().get(dependency.name());
        if (sig == null) {
            throw new IllegalStateException("`" + dependency + "` is held by a behavior of its own"
                    + " module and has no signature there");
        }
        return BehaviorAbi.heldAs(dependency, sig.inputTypes());
    }

    /**
     * The members of {@code answers} that reach its union through a bridge case of this module, in
     * the order the union lists them, each with the class a caller tests against and the accessor it
     * reads the member back through.
     */
    private static List<LinkageProjection.Bridged> answeredThrough(Settled settled, Type answers,
                                                                   LinkageReader foreign) {
        if (!(answers instanceof Type.Union)) {
            return List.of();
        }
        List<LinkageProjection.Bridged> out = new ArrayList<>();
        for (TypeSymbol member : AtomSpace.subjectAtoms(answers, settled.published())) {
            if (!member.isDeclaredByLanguage() && member instanceof TypeSymbol.AtModule at
                    && at.module().equals(settled.module())) {
                continue;
            }
            ClassDesc bridge = classOf(new GeneratedClass.BridgeCase(settled.module(), member),
                    foreign);
            out.add(new LinkageProjection.Bridged(member, bridge.descriptorString(),
                    MethodTypeDesc.of(JvmTypes.jvmType(TypeOps.caseBindType(member),
                            t -> typeClass(t, foreign))).descriptorString()));
        }
        return out;
    }

    private static LinkageProjection.Data data(Settled settled, TypeKey declaration,
                                               LinkageReader foreign) {
        Hir.Def def = settled.symbols().declaredNode(declaration);
        if (def == null) {
            throw new IllegalStateException("`" + declaration + "` is declared and has no settled"
                    + " declaration");
        }
        String carrier = classOf(new GeneratedClass.Value(def.declares()), foreign)
                .descriptorString();
        boolean exposed = settled.exposes(def.name());
        return switch (def) {
            case Hir.Data data -> {
                List<LinkageProjection.Field> fields = laidOut(data, settled.symbols());
                yield new LinkageProjection.Data(data.declaredKey(),
                        data.newtype() ? LinkageProjection.Form.NEWTYPE
                                : LinkageProjection.Form.PRODUCT,
                        exposed, carrier, fields, List.of(),
                        Optional.of(construction(carrier, fields, foreign)));
            }
            case Hir.SumData sum -> new LinkageProjection.Data(sum.declaredKey(),
                    LinkageProjection.Form.SUM, exposed, carrier,
                    shared(sum, settled), cases(sum), Optional.empty());
            case Hir.UnitData unit -> new LinkageProjection.Data(unit.declaredKey(),
                    LinkageProjection.Form.UNIT, exposed, carrier, List.of(), List.of(),
                    Optional.empty());
        };
    }

    /**
     * The entry every class builds a product or a newtype through, its own module's excepted where
     * it builds one with nothing to check: {@code __construct}, taking the fields in the order a
     * value lays them out and answering the construction's {@code Result}.
     */
    private static LinkageProjection.Invocation construction(
            String carrier, List<LinkageProjection.Field> fields, LinkageReader foreign) {
        ClassDesc[] params = new ClassDesc[fields.size()];
        for (int i = 0; i < params.length; i++) {
            params[i] = JvmTypes.jvmType(fields.get(i).type(), t -> typeClass(t, foreign));
        }
        return LinkageProjection.Invocation.of(LinkageProjection.Opcode.STATIC,
                ClassDesc.ofDescriptor(carrier), "__construct",
                MethodTypeDesc.of(Descriptors.CD_Result, params));
    }

    /** A product's fields in the order a value lays them out, which is the order its constructor
     *  and {@code __construct} take them. */
    private static List<LinkageProjection.Field> laidOut(Hir.Data data, DerivedSymbols symbols) {
        Map<String, Type> types = TypeOps.fieldTypes(data, symbols);
        List<LinkageProjection.Field> out = new ArrayList<>();
        for (String field : TypeOps.fieldLayout(data, symbols)) {
            out.add(new LinkageProjection.Field(field, types.get(field)));
        }
        return out;
    }

    /** The fields a sum exposes because every case spreads them, which its interface declares. */
    private static List<LinkageProjection.Field> shared(Hir.SumData sum, Settled settled) {
        List<LinkageProjection.Field> out = new ArrayList<>();
        if (TypeView.asWritten(Type.ref(sum.declares()), settled.symbols(), settled.published())
                .shape() instanceof Shape.Sum shape) {
            ReadableFields.of(shape).declaredFields().forEach((field, type) ->
                    out.add(new LinkageProjection.Field(field, type)));
        }
        return out;
    }

    private static List<TypeSymbol> cases(Hir.SumData sum) {
        List<TypeSymbol> out = new ArrayList<>();
        for (Hir.Name name : sum.cases()) {
            out.add(Backend.names(name));
        }
        return out;
    }

    /** The class {@code generated} is called, recorded where it is of another module. */
    private static ClassDesc classOf(GeneratedClass generated, LinkageReader foreign) {
        foreign.named(generated);
        return SoutherJvmAbi.nameOf(generated).classDesc();
    }

    private static ClassDesc typeClass(TypeSymbol type, LinkageReader foreign) {
        return classOf(new GeneratedClass.Value(type), foreign);
    }
}
