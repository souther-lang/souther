package souther.compiler;

import tools.jackson.databind.JsonNode;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * Where a later copy of a schema accepts fewer documents than the copy that shipped.
 *
 * <p>The rule a frozen {@code schemaVersion} is held to (spec, the adequacy report's versioning): the
 * documents it accepts may grow and must not shrink. This is not a decision of that for JSON Schema
 * at large, and refuses to look like one. It knows the ways this repository grows a schema — a key
 * added to an object's {@code properties}, a definition added to {@code $defs}, a word added to an
 * {@code enum}, a key taken out of {@code required} — and the one thing that changes nothing a
 * document is held to, a {@code description}. Everything else has to be as it shipped. So a change
 * that grows the set in a way not listed here is named as a narrowing too, and is a decision
 * somebody makes here rather than one that passes unread.
 */
public final class SchemaEvolution {

    private SchemaEvolution() {
    }

    /** Each place {@code current} accepts less than {@code shipped} did, by its path from the root. */
    public static List<String> narrowings(JsonNode shipped, JsonNode current) {
        List<String> out = new ArrayList<>();
        compare(shipped, current, "", out);
        return out;
    }

    private static void compare(JsonNode shipped, JsonNode current, String at, List<String> out) {
        if (shipped.isObject() && current.isObject()) {
            for (String key : shipped.propertyNames()) {
                if (key.equals("description")) {
                    continue;
                }
                String here = at + "/" + key;
                if (!current.has(key)) {
                    out.add(here + ": no longer here");
                    continue;
                }
                switch (key) {
                    // Fewer keys a document must carry is more documents.
                    case "required" -> {
                        Set<String> added = words(current.get(key));
                        added.removeAll(words(shipped.get(key)));
                        if (!added.isEmpty()) {
                            out.add(here + ": now requires " + added);
                        }
                    }
                    // More words a field may carry is more documents.
                    case "enum" -> {
                        Set<String> gone = words(shipped.get(key));
                        gone.removeAll(words(current.get(key)));
                        if (!gone.isEmpty()) {
                            out.add(here + ": no longer allows " + gone);
                        }
                    }
                    // Each name as it shipped, and names added beside them.
                    case "properties", "$defs" -> {
                        for (String name : shipped.get(key).propertyNames()) {
                            if (!current.get(key).has(name)) {
                                out.add(here + "/" + name + ": no longer here");
                            } else {
                                compare(shipped.get(key).get(name), current.get(key).get(name),
                                        here + "/" + name, out);
                            }
                        }
                    }
                    default -> compare(shipped.get(key), current.get(key), here, out);
                }
            }
            for (String key : current.propertyNames()) {
                if (!shipped.has(key) && !key.equals("description")) {
                    out.add(at + "/" + key + ": not in what shipped");
                }
            }
        } else if (shipped.isArray() && current.isArray()) {
            if (shipped.size() != current.size()) {
                out.add(at + ": " + shipped.size() + " entries shipped and " + current.size()
                        + " now");
                return;
            }
            for (int i = 0; i < shipped.size(); i++) {
                compare(shipped.get(i), current.get(i), at + "/" + i, out);
            }
        } else if (!shipped.equals(current)) {
            out.add(at + ": " + shipped + " shipped and " + current + " now");
        }
    }

    private static Set<String> words(JsonNode array) {
        Set<String> out = new LinkedHashSet<>();
        array.forEach(each -> out.add(each.asString()));
        return out;
    }
}
