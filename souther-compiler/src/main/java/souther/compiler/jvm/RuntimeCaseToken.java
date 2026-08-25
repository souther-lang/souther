package souther.compiler.jvm;

/**
 * How a case is named where a generated class and souther-runtime pass one between them.
 *
 * <p>Not a class name and not a source spelling. A behavior answering a union carries which case it
 * answered out of the run, and what carries it is a pair of strings: the constant a generated
 * comparison is written against, and the two arguments a {@code souther.runtime.DeclaredCase} is
 * built from. Both are read by code that is already compiled, so the spelling is a protocol and not
 * a decision anything downstream may retake.
 *
 * <p>{@code namespace} and not {@code module}, because what stands there for a case the language
 * gives is no module: {@code DivisionByZero} is written under {@code souther.runtime} because that
 * is what the pair has always said, and there is no module of that name. The runtime's own record
 * calls the field {@code module}, which is the name the schema was written under and is left where
 * it is — renaming it would change the protocol to say something truer about a compiler that is not
 * the one reading old jars.
 */
public record RuntimeCaseToken(String namespace, String name) {

    public RuntimeCaseToken {
        if (namespace == null || name == null) {
            throw new IllegalArgumentException(
                    "a case token is a namespace and a name: " + namespace + "." + name);
        }
    }

    /** Both parts, as the generated comparison writes them. */
    public String qualified() {
        return namespace + "." + name;
    }

    @Override
    public String toString() {
        return qualified();
    }
}
