package souther.runtime.meta;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * A data definition, carried on the class it generated, as the Souther source that declared it.
 *
 * <p>It is the source rather than a structure because the declaration surface is recursive —
 * {@code List<Map<K, V>>} nests, and so does a decoder reference — and an annotation type may not
 * have an element of its own type. Types and invariants would end up as text whatever the shape
 * around them was, and the text is read back by the parser that already exists.
 */
@Retention(RetentionPolicy.CLASS)
@Target(ElementType.TYPE)
public @interface SoutherData {

    /** The definition as written: {@code data Amount = Int} and its {@code invariant}, its fields,
     * its {@code decoder}/{@code encoder} blocks — whatever the author wrote. */
    String value();
}
