package souther.architecture;

import java.lang.classfile.ClassModel;
import java.lang.classfile.MethodModel;
import java.lang.constant.MethodTypeDesc;

/**
 * Which method a row of a check is about, said so that no two methods say it alike.
 *
 * <p>The class, the name and what it takes. A name alone is every overload of it at once, so a row
 * written by name is one row for all of them: a second overload arriving beside the first, or the
 * first going while the second stays, leaves the row where it was, and a map keyed by it keeps one
 * of the two and drops the other. What tells overloads apart is what they take, which is the
 * descriptor, so the descriptor is part of what a method is here.
 *
 * <p>Said in one place so that a check naming a method has one way to do it.
 */
final class AMethod {

    private AMethod() {}

    /** {@code method} of {@code owner}. */
    static String of(ClassModel owner, MethodModel method) {
        return of(owner.thisClass().asInternalName(), method.methodName().stringValue(),
                method.methodTypeSymbol());
    }

    /** The method {@code name} of the class {@code owner}, taking and answering as {@code type}
     *  says. */
    static String of(String owner, String name, MethodTypeDesc type) {
        return owner + "#" + name + type.descriptorString();
    }

    /** The same, with the descriptor written out. */
    static String of(String owner, String name, String descriptor) {
        return of(owner, name, MethodTypeDesc.ofDescriptor(descriptor));
    }
}
