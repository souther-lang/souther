package souther.compiler.coverage;

import souther.compiler.core.Core;
import souther.compiler.diag.SourceRef;
import souther.compiler.types.TypeName;

import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;

/**
 * The arms of a behavior's body that an {@code example} row can be in or not in.
 *
 * <p>What this counts is <em>branch-arm coverage</em>, and calling it anything larger would overstate
 * it. Passing through all four arms of
 *
 * <pre>if A { if B { X } else { Y } } else { Z }</pre>
 *
 * does not mean the interactions between A and B were tried, nor that every reachable path was. Branch
 * coverage is a lower bound on covering the paths a body has, not the same thing, and a report that
 * says "code paths" invites the author to stop looking.
 *
 * <p>An {@code unreachable} arm gets no site. Reaching one is already an error ({@code E1911}), so a
 * probe there would leave every correct model permanently one arm short and make the denominator lie.
 * An invariant clause gets none either: it is a property of a type, not a fork in this body, and
 * whether the rows reach its edges is a different measure asked another way.
 *
 * <p>A {@code guard … else} is an {@code if} by the time it gets here, so it needs no case of its own.
 * Helper bodies are not walked: a non-recursive helper is already inlined into the body that uses it,
 * and a recursive one is a shared method rather than a fork in any one behavior.
 */
public final class CoverageSites {

    /**
     * One arm.
     *
     * @param index       what identifies it in this run — the probe number, and what a hit set holds
     * @param ordinal     where it comes in its behavior, for display
     * @param fingerprint what the arm is made of, ignoring where it is written. Kept for a later
     *                    version to match one run's sites against another's, and not used as identity
     *                    here: two structurally identical arms in one behavior have the same one, and
     *                    mixing the position back in would change it whenever a line is added above.
     */
    public record Site(String behavior, Kind kind, String label, SourceRef at,
                       int index, int ordinal, String fingerprint) {

        public enum Kind {
            /** The arm an {@code if} takes when its condition holds. */
            THEN,
            /** The arm it takes when the condition does not hold — a {@code guard}'s departure. */
            ELSE,
            /** One arm of a {@code match}. Cases written together on one arm are one site: they are
             * one run of code, and a row takes it or does not. */
            CASE,
            /** The arm an attempted construction takes when the value was built. */
            CONSTRUCTED,
            /** An arm it takes when a clause refused. */
            DEPARTURE
        }
    }

    /**
     * The two arms of one {@code if}, so that a threshold read off its condition can ask whether the
     * comparison was ever evaluated.
     *
     * <p>Reaching a value is not reaching a comparison. A row can hand a behavior the exact boundary
     * value and never get to the guard that cares about it, because an earlier branch went the other
     * way — so a boundary drawn by a guard is met only by a row that also lit one of these.
     */
    public record GuardRef(String behavior, int siteIndexThen, int siteIndexElse, SourceRef at) {}

    /**
     * Every site of a module, and how to find the ones belonging to a node.
     *
     * <p>{@code byNode} is keyed by identity. Core nodes are records, so two arms that look the same
     * are equal, and a value-keyed map would hand the emitter the wrong arm's probe. The instances
     * here must be the ones the emitter is walking — the same answer, not an equal one.
     */
    public record Plan(List<Site> sites, List<GuardRef> guards, IdentityHashMap<Core, int[]> byNode) {

        public static final Plan NONE = new Plan(List.of(), List.of(), new IdentityHashMap<>());

        public boolean isEmpty() {
            return sites.isEmpty();
        }

        /** The probe numbers of {@code node}'s arms, in the order the emitter emits them, or null
         * where this node has none. */
        public int[] probesOf(Core node) {
            return byNode.get(node);
        }

        public Site site(int index) {
            return sites.get(index);
        }
    }

    /** The sites of every behavior body in one module, numbered in the order the bodies are declared
     * and, within one, in the order the arms are written. */
    public static Plan of(String sourceId, Map<String, Core> behaviorBodies) {
        Walk walk = new Walk(sourceId);
        for (Map.Entry<String, Core> body : behaviorBodies.entrySet()) {
            walk.behavior(body.getKey(), body.getValue());
        }
        return new Plan(List.copyOf(walk.sites), List.copyOf(walk.guards), walk.byNode);
    }

    private static final class Walk {

        private final String sourceId;
        private final List<Site> sites = new ArrayList<>();
        private final List<GuardRef> guards = new ArrayList<>();
        private final IdentityHashMap<Core, int[]> byNode = new IdentityHashMap<>();
        private String behavior;
        private int ordinal;

        Walk(String sourceId) {
            this.sourceId = sourceId;
        }

        void behavior(String name, Core body) {
            this.behavior = name;
            this.ordinal = 0;
            walk(body);
        }

        private int site(Site.Kind kind, String label, Core arm) {
            int index = sites.size();
            sites.add(new Site(behavior, kind, label, new SourceRef(sourceId, arm.pos()),
                    index, ordinal++, Fingerprint.of(kind, label, arm)));
            return index;
        }

        /**
         * Written out rather than reusing {@link Core#forEachChild}: what is being numbered is a
         * {@code Case} and an {@code ElseArm}, which are not {@code Core} and so are not children the
         * generic walk hands over. The switch is exhaustive on purpose — a node added to the IR should
         * stop here and be decided about, not fall silently into a default and go uncounted.
         */
        private void walk(Core e) {
            switch (e) {
                case Core.Int _, Core.Decimal _, Core.Str _, Core.Bool _, Core.Read _,
                     Core.UnitValue _, Core.OptionNone _ -> { }
                // An arm that says nothing arrives here is not an arm to cover.
                case Core.Unreachable _ -> { }
                case Core.Neg n -> walk(n.operand());
                case Core.FieldAccess fa -> walk(fa.target());
                case Core.Binary b -> {
                    walk(b.left());
                    walk(b.right());
                }
                case Core.Call c -> c.args().forEach(this::walk);
                case Core.Apply a -> a.args().forEach(this::walk);
                case Core.LetIn li -> {
                    walk(li.value());
                    walk(li.body());
                }
                case Core.Block b -> walk(b.body());
                case Core.ListLit lit -> lit.elements().forEach(this::walk);
                case Core.OptionSome s -> walk(s.value());
                case Core.Tuple t -> t.elements().forEach(this::walk);
                case Core.TupleGet tg -> walk(tg.tuple());
                case Core.NewData nd -> nd.inits().forEach(init -> walk(init.value()));
                case Core.If iff -> {
                    walk(iff.cond());
                    int then = site(Site.Kind.THEN, "then", iff.then());
                    walk(iff.then());
                    int els = site(Site.Kind.ELSE, "else", iff.els());
                    walk(iff.els());
                    byNode.put(iff, new int[] {then, els});
                    guards.add(new GuardRef(behavior, then, els,
                            new SourceRef(sourceId, iff.pos())));
                }
                case Core.Match m -> {
                    walk(m.scrutinee());
                    int[] arms = new int[m.cases().size()];
                    for (int i = 0; i < m.cases().size(); i++) {
                        Core.Case arm = m.cases().get(i);
                        arms[i] = site(Site.Kind.CASE, label(arm), arm.body());
                        walk(arm.body());
                    }
                    byNode.put(m, arms);
                }
                case Core.IfConstructed ic -> {
                    ic.construct().inits().forEach(init -> walk(init.value()));
                    int[] arms = new int[1 + ic.els().size()];
                    arms[0] = site(Site.Kind.CONSTRUCTED, "constructed", ic.then());
                    walk(ic.then());
                    for (int i = 0; i < ic.els().size(); i++) {
                        Core.ElseArm arm = ic.els().get(i);
                        arms[i + 1] = site(Site.Kind.DEPARTURE, label(arm), arm.body());
                        walk(arm.body());
                    }
                    byNode.put(ic, arms);
                }
            }
        }

        private static String label(Core.Case arm) {
            List<String> names = arm.caseTypes().stream().map(TypeName::name).toList();
            return "case " + String.join(" | ", names);
        }

        private static String label(Core.ElseArm arm) {
            return arm.clause().map(c -> "else " + c).orElse("else");
        }
    }

    /**
     * What an arm is made of, said without saying where it is.
     *
     * <p>Positions are left out so that adding a line above an arm does not change it; the arm's own
     * shape is what is hashed. That leaves two arms with identical bodies in one behavior sharing a
     * fingerprint, which is why nothing here treats it as identity.
     */
    private static final class Fingerprint {

        static String of(Site.Kind kind, String label, Core arm) {
            StringBuilder out = new StringBuilder(kind.name()).append('/').append(label).append('/');
            shape(arm, out);
            return hex(out.toString());
        }

        private static void shape(Core e, StringBuilder out) {
            out.append(e.getClass().getSimpleName()).append('(');
            switch (e) {
                case Core.Int i -> out.append(i.value());
                case Core.Decimal d -> out.append(d.value());
                case Core.Str s -> out.append(s.value().length());
                case Core.Bool b -> out.append(b.value());
                case Core.Read r -> out.append(r.name());
                case Core.UnitValue u -> out.append(u.data());
                case Core.FieldAccess fa -> {
                    out.append(fa.field()).append(',');
                    shape(fa.target(), out);
                }
                case Core.Binary b -> {
                    out.append(b.op()).append(',');
                    shape(b.left(), out);
                    shape(b.right(), out);
                }
                case Core.Call c -> {
                    out.append(c.fn()).append(',');
                    c.args().forEach(a -> shape(a, out));
                }
                case Core.Apply a -> {
                    out.append(a.fn().name()).append(',');
                    a.args().forEach(x -> shape(x, out));
                }
                case Core.NewData nd -> {
                    out.append(nd.typeName()).append(',');
                    nd.inits().forEach(i -> {
                        out.append(i.name()).append('=');
                        shape(i.value(), out);
                    });
                }
                case Core.Match m -> {
                    shape(m.scrutinee(), out);
                    m.cases().forEach(c -> {
                        out.append(c.caseTypes()).append(':');
                        shape(c.body(), out);
                    });
                }
                case Core.If iff -> {
                    shape(iff.cond(), out);
                    shape(iff.then(), out);
                    shape(iff.els(), out);
                }
                case Core.IfConstructed ic -> {
                    shape(ic.construct(), out);
                    shape(ic.then(), out);
                    ic.els().forEach(arm -> shape(arm.body(), out));
                }
                case Core.Unreachable u -> out.append(u.reason());
                default -> Core.forEachChild(e, child -> shape(child, out));
            }
            out.append(')');
        }

        private static String hex(String of) {
            try {
                byte[] digest = java.security.MessageDigest.getInstance("SHA-256")
                        .digest(of.getBytes(StandardCharsets.UTF_8));
                StringBuilder out = new StringBuilder();
                for (int i = 0; i < 6; i++) {
                    out.append(String.format("%02x", digest[i]));
                }
                return out.toString();
            } catch (java.security.NoSuchAlgorithmException e) {
                throw new IllegalStateException("SHA-256 is required of every JVM", e);
            }
        }

        private Fingerprint() {}
    }

    private CoverageSites() {}
}
