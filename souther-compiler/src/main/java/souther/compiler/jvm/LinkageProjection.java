package souther.compiler.jvm;

import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;

import java.lang.constant.ClassDesc;
import java.lang.constant.MethodTypeDesc;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.function.Function;
import java.util.stream.Collectors;

/**
 * What one declaration offers the classes of another module on the JVM: the facts a class compiled
 * against it links by, and nothing a class elsewhere cannot see.
 *
 * <p>A class built against a module bakes in facts about the declarations it reaches — which class a
 * behavior is called on and by which instruction, what a constructor takes, how a type's fields are
 * laid out. This is those facts for one declaration, as the rules this compiler emits by make them
 * out of what the declaration settled. What a behavior's body computes and what an invariant states
 * are not here: they run inside the declaring module's classes, which a class elsewhere calls and
 * does not copy.
 *
 * <p>A projection says which facts depend on the declaration; the rules turning a declaration into
 * JVM facts are this compiler's, and a change to them is a change of {@code BOUNDARY_VERSION}, not
 * of any declaration. So two projections of one declaration differ exactly where a class compiled
 * against the one would link to something else in the other.
 *
 * <p>{@link #facts()} is the one written form. An artifact records a projection as its facts, and a
 * compilation reading the artifact compares facts: the types in a projection are held as the
 * compiler's own types, and turning a written type back into one is the front end's business, not a
 * second syntax kept here.
 */
public sealed interface LinkageProjection {

    /** The declaration this is a projection of. */
    LinkageTarget target();

    /**
     * What this says, in the order an artifact writes it: one fact per label, each written the way a
     * report shows it.
     *
     * <p>Every component is in here. Two projections with the same facts are one projection, and a
     * component left out would be a fact a class links by that an artifact does not record.
     *
     * <p>What is said is what stands under each label, and never where a fact stands among the
     * others ({@link LinkageRecord}). An order a class links by is said inside one fact's value.
     */
    List<Fact> facts();

    /** One labelled fact of a projection, as an artifact writes it and a report shows it. */
    record Fact(String label, String value) {
        public Fact {
            if (label == null || label.isEmpty() || value == null || value.isEmpty()) {
                throw new IllegalArgumentException("a fact has a label and a value: "
                        + label + " = " + value);
            }
        }
    }

    /**
     * An instruction a class elsewhere invokes a method with: which instruction, the class it names
     * as its descriptor, the method and its descriptor.
     *
     * <p>Held as the descriptors the JVM writes, so a projection is compared by what a class file
     * says and not by how the class-file library represents it.
     */
    record Invocation(Opcode opcode, String owner, String method, String descriptor) {

        public static Invocation of(Opcode opcode, ClassDesc owner, String method,
                                    MethodTypeDesc descriptor) {
            return new Invocation(opcode, owner.descriptorString(), method,
                    descriptor.descriptorString());
        }

        /** The class it names. */
        public ClassDesc ownerClass() {
            return ClassDesc.ofDescriptor(owner);
        }

        /** The method's type. */
        public MethodTypeDesc methodType() {
            return MethodTypeDesc.ofDescriptor(descriptor);
        }

        String shown() {
            return opcode.written() + " " + owner + "." + method + descriptor;
        }
    }

    /** The instructions a class elsewhere invokes a declaration's methods with. */
    enum Opcode {
        STATIC, VIRTUAL, INTERFACE;

        String written() {
            return switch (this) {
                case STATIC -> "invokestatic";
                case VIRTUAL -> "invokevirtual";
                case INTERFACE -> "invokeinterface";
            };
        }
    }

    /**
     * A behavior as another module's classes reach it.
     *
     * @param behavior        the behavior
     * @param realization     whether its classes hold an implementation, an interface nobody has
     *                        written one for, or a base Java extends
     * @param exposed         whether its module exposes it, which is whether its classes are public
     * @param takes           what it takes, in order
     * @param answers         what it answers
     * @param heldAs          the descriptor of the type a class holding it injected keeps it as,
     *                        and takes it in a constructor as
     * @param apply           what a caller applies an instance held as {@code heldAs} with: the
     *                        unary {@code Behavior}'s {@code apply} for one taking one input, and the
     *                        typed {@code apply} of its own class for any other number
     * @param construction    how a class elsewhere builds it, where it has an implementation to build
     * @param answeredThrough the bridge case each member of an output union that its own module did
     *                        not declare is reached through, in the order the union lists them
     */
    record Behavior(ValueName.Behavior behavior, Realization realization, boolean exposed,
                    List<Type> takes, Type answers, String heldAs, Invocation apply,
                    Optional<Construction> construction, List<Bridged> answeredThrough)
            implements LinkageProjection {

        public Behavior {
            takes = List.copyOf(takes);
            answeredThrough = List.copyOf(answeredThrough);
            if (construction.isPresent() != (realization == Realization.IMPLEMENTED)) {
                throw new IllegalArgumentException("`" + behavior + "` is " + realization
                        + ", and a class elsewhere builds a behavior exactly when it has an"
                        + " implementation to build");
            }
        }

        @Override
        public LinkageTarget target() {
            return new LinkageTarget.Behavior(behavior);
        }

        /** The type a class holding it keeps it as. */
        public ClassDesc heldAsClass() {
            return ClassDesc.ofDescriptor(heldAs);
        }

        @Override
        public List<Fact> facts() {
            List<Fact> facts = new ArrayList<>();
            facts.add(new Fact("realized as", realization.written()));
            facts.add(new Fact("exposed", String.valueOf(exposed)));
            facts.add(new Fact("takes", takes.stream().map(LinkageProjection::shown)
                    .collect(Collectors.joining(", ", "(", ")"))));
            facts.add(new Fact("answers", shown(answers)));
            facts.add(new Fact("held as", heldAs));
            facts.add(new Fact("applied by", apply.shown()));
            construction.ifPresent(built -> {
                facts.add(new Fact("built with", built.dependencies().stream()
                        .map(ValueName.Behavior::toString)
                        .collect(Collectors.joining(", ", "(", ")"))
                        + " through " + built.implementation() + built.constructor()));
                facts.add(new Fact("applied when built by", built.erasedApply().shown()));
            });
            for (Bridged bridged : answeredThrough) {
                facts.add(new Fact("answers " + shown(bridged.member()) + " through",
                        bridged.bridge() + ".value" + bridged.value()));
            }
            return List.copyOf(facts);
        }
    }

    /** Where a behavior's body is, as the classes of its module hold it. */
    enum Realization {
        /** An interface, and an implementation class behind it that a caller can build. */
        IMPLEMENTED,
        /** An interface and no implementation: Souther's to write, and nobody has. */
        UNWRITTEN,
        /** An abstract base Java extends; the caller is handed an instance. */
        SUPPLIED_BY_JAVA;

        String written() {
            return switch (this) {
                case IMPLEMENTED -> "implemented";
                case UNWRITTEN -> "unwritten";
                case SUPPLIED_BY_JAVA -> "supplied by Java";
            };
        }
    }

    /**
     * How a class elsewhere builds a behavior's implementation and applies what it built.
     *
     * @param implementation the descriptor of the class it instantiates
     * @param dependencies   what it hands the constructor, in the order the constructor takes them
     * @param constructor    the constructor's descriptor
     * @param erasedApply    the {@code apply} taking and answering objects, which a composition
     *                       applies a stage it built by
     */
    record Construction(String implementation, List<ValueName.Behavior> dependencies,
                        String constructor, Invocation erasedApply) {
        public Construction {
            dependencies = List.copyOf(dependencies);
        }

        /** The class it instantiates. */
        public ClassDesc implementationClass() {
            return ClassDesc.ofDescriptor(implementation);
        }

        /** The constructor's type. */
        public MethodTypeDesc constructorType() {
            return MethodTypeDesc.ofDescriptor(constructor);
        }
    }

    /**
     * A member of a behavior's output union reached through a bridge case of the behavior's module:
     * the descriptors of the class a caller tests the answer against and of the accessor it unwraps
     * the member with.
     */
    record Bridged(TypeSymbol member, String bridge, String value) {

        /** The class a caller tests the answer against. */
        public ClassDesc bridgeClass() {
            return ClassDesc.ofDescriptor(bridge);
        }

        /** The type of the accessor it unwraps the member with. */
        public MethodTypeDesc valueType() {
            return MethodTypeDesc.ofDescriptor(value);
        }
    }

    /**
     * A declared type as another module's classes reach it: the class, what a read of it finds, and
     * the entry they build one through.
     *
     * <p>Each fact is here because a class elsewhere decides something by it, and nothing is here
     * that only the type's own classes decide by. Whether building one runs a check is the second
     * kind: a class elsewhere builds it through {@code __construct} either way, since its constructor
     * is its own module's, so a type gaining or losing a rule leaves what that class links by as it
     * was.
     *
     * @param key          the declaration
     * @param form         which of the four it was declared as
     * @param exposed      whether its module exposes it, which is whether its class is public
     * @param carrier      the descriptor of the class a value of it is
     * @param fields       what a read of a value finds, in the order a value lays them out: a
     *                     product's fields, a newtype's one value, and the fields a sum exposes
     *                     because every case spreads them
     * @param cases        a sum's cases, in the order it declares them
     * @param construction the entry a class elsewhere builds one through — a product's and a
     *                     newtype's {@code __construct}; a sum is built as one of its cases and a
     *                     unit is its one value, so neither has one
     */
    record Data(TypeKey key, Form form, boolean exposed, String carrier, List<Field> fields,
                List<TypeSymbol> cases, Optional<Invocation> construction)
            implements LinkageProjection {

        public Data {
            fields = List.copyOf(fields);
            cases = List.copyOf(cases);
            boolean built = form == Form.PRODUCT || form == Form.NEWTYPE;
            if (construction.isPresent() != built) {
                throw new IllegalArgumentException("`" + key + "` is a " + form.written()
                        + ", and a class elsewhere builds exactly a product or a newtype through"
                        + " an entry");
            }
        }

        @Override
        public LinkageTarget target() {
            return new LinkageTarget.Data(key);
        }

        @Override
        public List<Fact> facts() {
            List<Fact> facts = new ArrayList<>();
            facts.add(new Fact("declared as", form.written()));
            facts.add(new Fact("exposed", String.valueOf(exposed)));
            facts.add(new Fact("carried as", carrier));
            if (form == Form.PRODUCT || form == Form.NEWTYPE) {
                // The order a constructor and __construct take the fields in, which two fields of
                // one type can trade places in with nothing else about them moving.
                facts.add(new Fact("laid out as", fields.stream().map(Field::name)
                        .collect(Collectors.joining(", ", "(", ")"))));
            }
            for (Field field : fields) {
                facts.add(new Fact("field " + field.name(), shown(field.type())));
            }
            if (!cases.isEmpty()) {
                facts.add(new Fact("cases", cases.stream().map(LinkageProjection::shown)
                        .collect(Collectors.joining(" | "))));
            }
            construction.ifPresent(entry -> facts.add(new Fact("built by", entry.shown())));
            return List.copyOf(facts);
        }
    }

    /** The four forms a declared type takes on the JVM. */
    enum Form {
        PRODUCT, NEWTYPE, SUM, UNIT;

        String written() {
            return switch (this) {
                case PRODUCT -> "product";
                case NEWTYPE -> "newtype";
                case SUM -> "sum";
                case UNIT -> "unit";
            };
        }
    }

    /** One field a read of a value finds. */
    record Field(String name, Type type) {}

    /**
     * A published value as another module's classes reach it: the entry that runs it where it is
     * declared, and what they take its answer as.
     */
    record Value(ValueName.Helper value, Invocation entry, Type answers)
            implements LinkageProjection {

        @Override
        public LinkageTarget target() {
            return new LinkageTarget.Value(value);
        }

        @Override
        public List<Fact> facts() {
            return List.of(new Fact("entered by", entry.shown()),
                    new Fact("answers", shown(answers)));
        }
    }

    /**
     * {@code type} with every declaration written by its module and name, so one written type is one
     * type whichever module wrote it down.
     */
    static String shown(Type type) {
        return Type.showAs(type, QUALIFIED, false);
    }

    /** {@code name} written by its module and name, or as the language spells it. */
    static String shown(TypeSymbol name) {
        return QUALIFIED.apply(name);
    }

    Function<TypeSymbol, String> QUALIFIED = name ->
            name instanceof TypeSymbol.AtModule at ? at.key().qualified() : name.name();
}
