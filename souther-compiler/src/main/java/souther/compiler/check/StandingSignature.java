package souther.compiler.check;

import souther.compiler.types.Type;

import java.util.List;

/**
 * What a call left standing is typed against: the type its declaration states, and the names that
 * declaration gave its parameters.
 *
 * <p>Two answers and not one. The type is what typing reads, and two declarations naming their
 * parameters differently declare one type; the names are what a report about an argument says it
 * was handed to. Held inside the type, they would make two types of one.
 */
public record StandingSignature(List<String> parameters, Type.FnOf type) {

    public StandingSignature {
        parameters = List.copyOf(parameters);
        if (parameters.size() != type.params().size()) {
            throw new IllegalArgumentException("a declaration names each parameter it types: "
                    + parameters + " against " + Type.show(type));
        }
    }
}
