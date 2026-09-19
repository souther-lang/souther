package souther.architecture;

import java.lang.classfile.ClassModel;
import java.lang.classfile.FieldModel;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The fields of a class whose declared type is a kind of {@code java.util.Map} or
 * {@code java.util.Set}.
 *
 * <p>What a rule about one carrier asks of it, so that each of them does not carry its own reading
 * of what a {@code Map} or a {@code Set} is. It says nothing about which carriers are asked: that is
 * each rule's to name, by naming the class, and a list of them kept here would be a list somebody has
 * to remember to add to.
 *
 * <p><b>Asked of the type and not of a list of names.</b> A field typed through the interface is not
 * the only way a map comes back — a platform implementation nobody named by hand, or a custom class
 * implementing either, holds exactly the same salted order — so the field's own type is loaded and
 * asked whether it is a kind of either.
 *
 * <p>A type this cannot load is not a type proved to be neither: it is a question this cannot
 * answer, and it fails rather than passing while silent about it, the way
 * {@link CompiledOutputs#read} does for a class it was asked for and never built.
 */
final class MapOrSetFields {

    private MapOrSetFields() {
    }

    /** Every field of {@code model} typed as a kind of {@code Map} or {@code Set}, as its class, its
     *  name and its descriptor. */
    static List<String> in(ClassModel model) {
        List<String> found = new ArrayList<>();
        for (FieldModel field : model.fields()) {
            String descriptor = field.fieldTypeSymbol().descriptorString();
            if (descriptor.startsWith("L") && descriptor.endsWith(";")
                    && isAMapOrASet(descriptor.substring(1, descriptor.length() - 1))) {
                found.add(model.thisClass().name().stringValue() + "#"
                        + field.fieldName().stringValue() + " " + descriptor);
            }
        }
        return found;
    }

    private static boolean isAMapOrASet(String internalName) {
        String named = internalName.replace('/', '.');
        try {
            Class<?> loaded = Class.forName(named, false, MapOrSetFields.class.getClassLoader());
            return Map.class.isAssignableFrom(loaded) || Set.class.isAssignableFrom(loaded);
        } catch (ClassNotFoundException | LinkageError unresolved) {
            throw new AssertionError(
                    "whether " + named + " is a kind of Map or Set could not be settled, so this"
                            + " rule cannot say the field it types is neither", unresolved);
        }
    }
}
