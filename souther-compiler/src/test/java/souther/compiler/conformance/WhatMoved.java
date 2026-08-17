package souther.compiler.conformance;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * Which answer moved, said in the words the report says it in.
 *
 * <p>A difference between two of these documents is read by someone deciding whether their change
 * was meant to move that. What they need to decide it is the module, the behavior and the measure —
 * and a line number in a JSON document is none of those, so a reader handed one opens the file and
 * works out where in the report it landed. That is the work this saves, and it is the whole reason
 * the answers are held here rather than compared by eye somewhere else.
 *
 * <p>The path is built from the identity each part of the report already carries — a module by its
 * {@code module}, a behavior by its {@code name}, an axis or a boundary by its {@code axis}. Read
 * off the document rather than written down here, so a report that grows a part cannot leave this
 * naming positions in an array.
 */
final class WhatMoved {

    /** The keys a part of the report identifies itself by, most specific first. */
    private static final List<String> IDENTITIES = List.of("module", "name", "axis");

    /** Enough to act on. A change to the shape of the report moves every part of it at once, and a
     *  reader handed all of them learns no more than from the first few and the count. */
    private static final int SHOWN = 12;

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private WhatMoved() {
    }

    /** What differs between two reports, in report terms, or empty where the two agree. */
    static List<String> between(String expected, String actual) {
        List<String> said = new ArrayList<>();
        walk("", JSON.readTree(expected), JSON.readTree(actual), said);
        if (said.size() <= SHOWN) {
            return said;
        }
        List<String> shown = new ArrayList<>(said.subList(0, SHOWN));
        shown.add("... and " + (said.size() - SHOWN) + " more");
        return shown;
    }

    private static void walk(String path, JsonNode was, JsonNode now, List<String> said) {
        if (was == null) {
            said.add(at(path) + "is answered now and was not written down: " + brief(now));
            return;
        }
        if (now == null) {
            said.add(at(path) + "was written down and is not answered now: " + brief(was));
            return;
        }
        if (was.isObject() && now.isObject()) {
            Set<String> fields = new LinkedHashSet<>();
            was.propertyNames().forEach(fields::add);
            now.propertyNames().forEach(fields::add);
            for (String field : fields) {
                walk(join(path, field), was.get(field), now.get(field), said);
            }
            return;
        }
        if (was.isArray() && now.isArray()) {
            walkArray(path, was, now, said);
            return;
        }
        if (!was.equals(now)) {
            said.add(at(path) + "was " + brief(was) + ", now " + brief(now));
        }
    }

    /**
     * Two arrays of the report, matched by what their members call themselves.
     *
     * <p>By identity rather than by position wherever the members carry one. Matched by position, a
     * behavior added at the front would report every behavior after it as changed, and the reader
     * would be told that everything moved when one thing was inserted.
     */
    private static void walkArray(String path, JsonNode was, JsonNode now, List<String> said) {
        if (allScalar(was) && allScalar(now)) {
            walkAsMembers(path, was, now, said);
            return;
        }
        Set<String> before = identitiesOf(was);
        Set<String> after = identitiesOf(now);
        if (before == null || after == null) {
            walkByPosition(path, was, now, said);
            return;
        }
        // The union, because a member that only one of them holds is the difference to report. Asked
        // of the two together — "are these the same identities" — a removal would answer no and send
        // both arrays to be matched by position, which reports the one that left and every member
        // after it as having moved.
        Set<String> all = new LinkedHashSet<>(before);
        all.addAll(after);
        for (String identity : all) {
            walk(join(path, identity), memberNamed(was, identity), memberNamed(now, identity), said);
        }
    }

    /**
     * What the members of one array call themselves, or null where they cannot be matched by name.
     *
     * <p>Of one array, not of two. Whether these members name themselves is a fact about this array,
     * and answering it about a pair makes every difference between the pair look like a reason not
     * to trust the names.
     *
     * <p>Null where any member names nothing, and where two name the same thing: a duplicate leaves
     * no way to say which of them a difference is about.
     */
    private static Set<String> identitiesOf(JsonNode array) {
        Set<String> out = new LinkedHashSet<>();
        for (JsonNode member : array) {
            String identity = identityOf(member).orElse(null);
            if (identity == null || !out.add(identity)) {
                return null;
            }
        }
        return out;
    }

    /**
     * A list of plain values, said as what joined it and what left it.
     *
     * <p>These are the report's sets — the classes an axis covers, the cases an output was
     * specified with. Compared by position, one member leaving is every member after it moving, and
     * the reader is told that three things changed when one class stopped being covered.
     */
    private static void walkAsMembers(String path, JsonNode was, JsonNode now, List<String> said) {
        Set<String> before = new LinkedHashSet<>();
        was.forEach(member -> before.add(member.toString()));
        Set<String> after = new LinkedHashSet<>();
        now.forEach(member -> after.add(member.toString()));
        List<String> gone = before.stream().filter(m -> !after.contains(m)).toList();
        List<String> joined = after.stream().filter(m -> !before.contains(m)).toList();
        if (!gone.isEmpty()) {
            said.add(at(path) + "no longer holds " + String.join(", ", gone));
        }
        if (!joined.isEmpty()) {
            said.add(at(path) + "now holds " + String.join(", ", joined));
        }
    }

    private static boolean allScalar(JsonNode array) {
        for (JsonNode member : array) {
            if (member.isObject() || member.isArray()) {
                return false;
            }
        }
        return true;
    }

    private static void walkByPosition(String path, JsonNode was, JsonNode now, List<String> said) {
        if (was.size() != now.size()) {
            said.add(at(path) + "held " + was.size() + " and now holds " + now.size());
        }
        for (int i = 0; i < Math.max(was.size(), now.size()); i++) {
            walk(path + "[" + i + "]", i < was.size() ? was.get(i) : null,
                    i < now.size() ? now.get(i) : null, said);
        }
    }

    private static java.util.Optional<String> identityOf(JsonNode member) {
        if (!member.isObject()) {
            return java.util.Optional.empty();
        }
        for (String key : IDENTITIES) {
            JsonNode value = member.get(key);
            if (value != null && value.isString()) {
                return java.util.Optional.of(value.stringValue());
            }
        }
        return java.util.Optional.empty();
    }

    private static JsonNode memberNamed(JsonNode array, String identity) {
        for (JsonNode member : array) {
            if (identityOf(member).filter(identity::equals).isPresent()) {
                return member;
            }
        }
        return null;
    }

    private static String join(String path, String segment) {
        return path.isEmpty() ? segment : path + " / " + segment;
    }

    private static String at(String path) {
        return path.isEmpty() ? "the report " : path + ": ";
    }

    /** A value short enough to read in a failure. */
    private static String brief(JsonNode node) {
        String written = node.toString();
        return written.length() <= 80 ? written : written.substring(0, 77) + "...";
    }
}
