package souther.compiler.meta;

import souther.compiler.copied.CopyRecord;
import souther.compiler.copied.CopyTarget;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.function.Function;

/**
 * Whether what the classes of a compiled module copied of other modules' declarations is what the
 * declarations a compilation has offer to be copied.
 *
 * <p>The copy half of what a module was built against, beside {@link LinkageAgreement}, which holds
 * what its classes link by. Nothing here knows what a copy holds: what a declaration is copied as is
 * decided where it is made, and this compares what was recorded with what is offered.
 */
public final class CopyAgreement {

    private CopyAgreement() {}

    /**
     * What holding the copies came to.
     *
     * @param disagreements each declaration the classes copied that is not offered as it was
     * @param complete      whether every declaration they copied could be held — false where a module
     *                      declaring one is not in the compilation, which is said where that is found
     */
    public record Held(List<Disagreement> disagreements, boolean complete) {
        public Held {
            disagreements = List.copyOf(disagreements);
        }
    }

    /** A declaration the classes copied that is not offered as it was. */
    public sealed interface Disagreement {

        /** The declaration. */
        CopyTarget target();

        /** Its module offers nothing of its kind under its name to be copied. */
        record NotProvided(CopyTarget target) implements Disagreement {}

        /** A value copied as a constant folds to another one: {@code was} and {@code now} as a source
         *  writes them, which is something a reader can hold against the source. */
        record AnotherConstant(CopyTarget target, String was, String now) implements Disagreement {
            public AnotherConstant {
                if (was.equals(now)) {
                    throw new IllegalArgumentException(target.shown() + " folds to what it did");
                }
            }
        }

        /** It is offered, and not as it was copied. What a body is copied as is not something a
         *  reader could hold against the source, so what is said is the form it was copied in. */
        record Moved(CopyTarget target, CopyRecord was, CopyRecord now) implements Disagreement {
            public Moved {
                if (was.equals(now)) {
                    throw new IllegalArgumentException(target.shown() + " is offered as it was");
                }
            }
        }
    }

    /**
     * Holds {@code copied} to what each declaration's module offers.
     *
     * @param copied     what the classes copied, by the declaration
     * @param providedBy what a module offers to be copied, by the declaration — or null where the
     *                   compilation does not hold the module
     */
    public static Held of(Map<CopyTarget, CopyRecord> copied,
                          Function<String, Map<CopyTarget, CopyRecord>> providedBy) {
        List<Disagreement> out = new ArrayList<>();
        boolean complete = true;
        for (Map.Entry<CopyTarget, CopyRecord> each : copied.entrySet()) {
            CopyTarget target = each.getKey();
            Map<CopyTarget, CopyRecord> offered = providedBy.apply(target.module());
            if (offered == null) {
                complete = false;
                continue;
            }
            CopyRecord was = each.getValue();
            CopyRecord now = offered.get(target);
            if (now == null) {
                out.add(new Disagreement.NotProvided(target));
            } else if (!now.equals(was)) {
                out.add(was.form() == CopyRecord.Form.CONSTANT
                        && now.form() == CopyRecord.Form.CONSTANT
                        ? new Disagreement.AnotherConstant(target, was.content(), now.content())
                        : new Disagreement.Moved(target, was, now));
            }
        }
        return new Held(out, complete);
    }
}
