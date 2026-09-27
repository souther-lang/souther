package souther.compiler.copied;

import souther.compiler.ast.Hir;
import souther.compiler.types.ValueName;

import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.HashMap;
import java.util.HexFormat;
import java.util.Map;
import java.util.TreeSet;
import java.util.function.Function;

/**
 * What each value of a module rests on, as a digest: the copy the value is offered as, and what
 * each value that copy names rests on.
 *
 * <p>For a clause that names a value and does not expand it. Expanded, a clause holds the value's
 * body, so it moves with everything the value is made of. Named, it would hold the name and move
 * with nothing, and a reader that copied the clause would go on holding a value that had changed.
 * Written with this beside the name it moves with the same things, and stays as long as its source
 * however many values name one another and however many times.
 *
 * <p>Each value is worked out once, from the values it names, so a chain of values in which each
 * names the one before it twice takes as many steps as it has links. A digest is of what the value
 * is offered as ({@link CopyRecord}): a constant is its number and rests on nothing, and a value
 * held as its body rests on the values that body names.
 */
public final class ValueDigests {

    private final String module;
    private final Map<String, Hir.FnDef> values;
    private final Function<String, CopyRecord> offeredAs;
    private final Map<String, String> worked = new HashMap<>();

    private ValueDigests(String module, Map<String, Hir.FnDef> values,
                         Function<String, CopyRecord> offeredAs) {
        this.module = module;
        this.values = values;
        this.offeredAs = offeredAs;
    }

    /**
     * @param module    the module whose values these are
     * @param values    each value of it that is offered to be copied, by its name, as its closed
     *                  definition
     * @param offeredAs what each of them is offered as, by its name
     * @return what each value rests on, or null for a name that is no value offered
     */
    public static Function<ValueName.Helper, String> over(String module,
                                                         Map<String, Hir.FnDef> values,
                                                         Function<String, CopyRecord> offeredAs) {
        ValueDigests digests = new ValueDigests(module, Map.copyOf(values), offeredAs);
        return helper -> helper.module().equals(module) && digests.values.containsKey(helper.name())
                ? digests.of(helper.name()) : null;
    }

    private String of(String value) {
        String known = worked.get(value);
        if (known != null) {
            return known;
        }
        CopyRecord offered = offeredAs.apply(value);
        MessageDigest digest = sha256();
        update(digest, offered.form().written());
        update(digest, offered.content());
        if (offered.form() != CopyRecord.Form.CONSTANT) {
            TreeSet<String> naming = new TreeSet<>();
            named(values.get(value), naming);
            for (String each : naming) {
                update(digest, each);
                update(digest, of(each));
            }
        }
        String written = HexFormat.of().formatHex(digest.digest());
        worked.put(value, written);
        return written;
    }

    /** The values of the module that {@code def} names, by name. */
    private void named(Hir.FnDef def, TreeSet<String> into) {
        if (def.body() instanceof Hir.FnBody.Written written) {
            walk(written.expr(), into);
        }
    }

    private void walk(Hir.Expr e, TreeSet<String> into) {
        if (e instanceof Hir.Var.Denoting named && named.denotes() instanceof ValueName.Helper helper
                && helper.module().equals(module) && values.containsKey(helper.name())) {
            into.add(helper.name());
        }
        Hir.forEachChild(e, child -> walk(child, into));
    }

    private static MessageDigest sha256() {
        try {
            return MessageDigest.getInstance("SHA-256");
        } catch (NoSuchAlgorithmException e) {
            throw new IllegalStateException("every Java platform has SHA-256", e);
        }
    }

    /** Length first, so two texts run together are not one text cut somewhere else. */
    private static void update(MessageDigest digest, String text) {
        byte[] bytes = text.getBytes(StandardCharsets.UTF_8);
        digest.update((byte) (bytes.length >>> 24));
        digest.update((byte) (bytes.length >>> 16));
        digest.update((byte) (bytes.length >>> 8));
        digest.update((byte) bytes.length);
        digest.update(bytes);
    }
}
