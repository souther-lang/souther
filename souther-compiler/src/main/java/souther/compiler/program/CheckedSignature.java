package souther.compiler.program;

import souther.compiler.types.Type;

import java.util.List;
import java.util.Objects;
import java.util.Optional;

/**
 * What a behavior takes and what it answers, as the check settled them.
 *
 * <p>Written here rather than handing over the compiler's own {@code Sig}. That one carries how a
 * value crosses the boundary as well as its type — for a {@code Map} key, which reading admitted
 * it — and the witness it holds for that offers the vocabulary the name was admitted from, which is
 * the module as it was parsed. So a reader of a signature could reach the syntax tree, two hops
 * from a behavior's declared output.
 *
 * <p>What an output needs is not only the type. Representation is a function of a value and the
 * position it stands at — an {@code Option} at a parameter and one nested in a list cross
 * differently, and a sum's alternatives travel as a bare tag or a discriminated object depending
 * on what they carry — so a reader asking how a value crosses reads {@link #inputs()} and
 * {@link #output()}, which are the checked boundary shape and carry that decision rather than
 * leaving it to be read off {@link Type} again. {@link #takes()} and {@link #answers()} stay for a
 * reader that only ever wanted the type.
 *
 * <p>Made one of two ways, as the behavior was written. A behavior that wrote a parameter list is
 * made from its {@link Parameter}s, and its inputs are read off them, so a parameter's name and the
 * input it stands for are one value and not two lists a reader lines up by position. A {@code >->}
 * composition writes no parameter list — its inputs are its first stage's — so it is made from the
 * inputs alone and {@link #declaredParameters()} says there is no declaration to name them.
 */
public final class CheckedSignature {

    /**
     * One parameter as the behavior's signature declares it: the name it is written under, and what
     * it can arrive as.
     *
     * <p>The name is the signature's and not a body's. A {@code let} implementing the behavior binds
     * its inputs by position under names of its own ({@link CheckedImplementation.Body#parameters}),
     * and a behavior with no body binds none; the name here is the one the declaration wrote, which
     * is the one a caller outside Souther can address the parameter by.
     */
    public static final class Parameter {

        private final String name;
        private final CheckedBoundaryInput input;

        Parameter(String name, CheckedBoundaryInput input) {
            this.name = Objects.requireNonNull(name);
            this.input = Objects.requireNonNull(input);
        }

        /** What the signature calls this parameter. */
        public String name() {
            return name;
        }

        /** What it can arrive as. */
        public CheckedBoundaryInput input() {
            return input;
        }

        /** The type it has, read off the shape as every type is. */
        public Type type() {
            return input.type();
        }

        @Override
        public boolean equals(Object other) {
            return other instanceof Parameter parameter
                    && name.equals(parameter.name) && input.equals(parameter.input);
        }

        @Override
        public int hashCode() {
            return Objects.hash(name, input);
        }

        @Override
        public String toString() {
            return name + ": " + input.type();
        }
    }

    private final List<CheckedBoundaryInput> inputs;
    private final Optional<List<Parameter>> declaredParameters;
    private final CheckedBoundaryOutput output;

    private CheckedSignature(List<CheckedBoundaryInput> inputs,
                             Optional<List<Parameter>> declaredParameters,
                             CheckedBoundaryOutput output) {
        this.inputs = inputs;
        this.declaredParameters = declaredParameters;
        this.output = output;
    }

    /** The signature of a behavior that wrote {@code parameters}, whose inputs are theirs. */
    static CheckedSignature declared(List<Parameter> parameters, CheckedBoundaryOutput output) {
        List<Parameter> declared = List.copyOf(parameters);
        return new CheckedSignature(declared.stream().map(Parameter::input).toList(),
                Optional.of(declared), output);
    }

    /** The signature of a composition, which takes {@code inputs} and names none of them. */
    static CheckedSignature composed(List<CheckedBoundaryInput> inputs,
                                     CheckedBoundaryOutput output) {
        return new CheckedSignature(List.copyOf(inputs), Optional.empty(), output);
    }

    /** What each parameter can arrive as, in the order they were declared. */
    public List<CheckedBoundaryInput> inputs() {
        return inputs;
    }

    /**
     * The parameters the signature declares, in the order they are written, where it declares any.
     *
     * <p>Present for a behavior that wrote a parameter list, and empty inside for one that wrote
     * {@code ()}. Absent for a composition, which takes {@link #inputs()} without a declaration to
     * name them — a different thing from declaring none.
     */
    public Optional<List<Parameter>> declaredParameters() {
        return declaredParameters;
    }

    /** What the answer can leave as — for a behavior that can depart, the cases of the union it
     *  may answer (spec §unmarked-sum). */
    public CheckedBoundaryOutput output() {
        return output;
    }

    /** Its inputs' types, in the order they were declared. */
    public List<Type> takes() {
        return inputs.stream().map(CheckedBoundaryInput::type).toList();
    }

    /** What it answers with — for a behavior that can depart, the union of every case it may
     *  answer (spec §unmarked-sum). */
    public Type answers() {
        return output.type();
    }

    @Override
    public String toString() {
        return declaredParameters.map(Object::toString).orElseGet(() -> takes().toString())
                + " -> " + answers();
    }
}
