package souther.compiler.generated;

import java.util.Map;
import java.util.Objects;

/**
 * What an example run is given to run against: the classes it loads, and what the compile that
 * emitted them generated an implementation for.
 *
 * <p>One value because the two have to be of one compile. Taken apart, a run could be handed one
 * compile's classes beside another's manifest — and the pair would not disagree anywhere a reader
 * could see it, because a row asks the manifest whether anything applies its behavior and then asks
 * the loader for the class, so the mismatch arrives as a class that is not there or, worse, as a row
 * recorded against a behavior that had something to run it. Made and passed as one, no caller has to
 * keep the two together.
 *
 * <p>Which module it is of is not settled here. A run is over one module's rows and this says nothing
 * about those, so the two being of one module is checked where both are in hand
 * ({@code ExampleVerifier.check}) rather than claimed by this type.
 *
 * <p>The two halves are not of the same extent, and that is the contract:
 * {@link #implementations}{@code .module()} is the module being evaluated, and {@link #classes} holds
 * that module's classes and additionally those of every module its rows can reach. A row applies a
 * behavior of the module it is written for and reaches the rest through generated code, so one
 * manifest is what a run needs — and one covering every linked module would be answering for
 * behaviors no answerer here is asked about.
 *
 * @param classes         binary name to bytecode, for this module and the ones its rows reach
 * @param implementations what the module being evaluated generated an implementation for
 */
public record EvaluationArtifact(Map<String, byte[]> classes,
                                 GeneratedImplementations implementations) {

    public EvaluationArtifact {
        Objects.requireNonNull(classes, "a run says what classes it loads");
        Objects.requireNonNull(implementations,
                "a run says what the compile generated an implementation for");
    }
}
