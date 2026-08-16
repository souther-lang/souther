package souther.compiler.diag;

import java.util.Locale;

/**
 * A code a compile once emitted and no longer does.
 *
 * <p>Separate from {@link DiagnosticCode} so that a retired number cannot be emitted: what is here
 * has no constructor a site can name. It is kept rather than deleted because the number was
 * published — a reader who met it, or a tool that recorded it, still asks what it meant, and the
 * specification answers from a {@code [#eNNNN-removed]} section saying what replaced it.
 *
 * <p>The two lists are disjoint, which is what keeps a number from being reused for a second rule.
 */
public enum RetiredDiagnosticCode {

    E1001,
    E1003,
    E1302,
    E1401,
    E1505,
    E1601,
    E1801;

    /** The anchor of this code's retirement note in the specification. */
    public String docAnchor() {
        return name().toLowerCase(Locale.ROOT) + "-removed";
    }
}
