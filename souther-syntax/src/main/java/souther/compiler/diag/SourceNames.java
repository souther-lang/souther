package souther.compiler.diag;

import java.util.ArrayList;
import java.util.List;

/**
 * What to call each of the files a compile was handed, so that no two of them read the same.
 *
 * <p>A file's name in a diagnostic is a basename where that is enough, because a path is noise a
 * reader has to look past. It stops being enough as soon as a diagnostic names a second file: two
 * modules may each keep a {@code model.sou}, and told that the other statement is in {@code
 * model.sou} a reader has learned nothing — which is the problem naming the file was for.
 *
 * <p>So a name is the shortest tail of a path that no other file in the same compile shares, and a
 * whole path only where even that is shared. One file, or files that differ in their last segment,
 * keep their basenames.
 */
public final class SourceNames {

    private SourceNames() {}

    /** What to call each of {@code paths}, in the same order. */
    public static List<String> of(List<String> paths) {
        List<List<String>> split = new ArrayList<>(paths.size());
        for (String path : paths) {
            split.add(segmentsOf(path));
        }
        List<String> names = new ArrayList<>(paths.size());
        for (int i = 0; i < paths.size(); i++) {
            names.add(shortestUnique(split, i, paths.get(i)));
        }
        return List.copyOf(names);
    }

    /** The shortest tail of the {@code at}-th path that no other path here ends with. */
    private static String shortestUnique(List<List<String>> split, int at, String whole) {
        List<String> mine = split.get(at);
        for (int depth = 1; depth <= mine.size(); depth++) {
            if (sharedBy(split, at, depth) == 0) {
                return String.join("/", mine.subList(mine.size() - depth, mine.size()));
            }
        }
        return whole;
    }

    /** How many of the other paths end with the {@code at}-th path's last {@code depth} segments. */
    private static int sharedBy(List<List<String>> split, int at, int depth) {
        List<String> mine = split.get(at);
        List<String> tail = mine.subList(mine.size() - depth, mine.size());
        int shared = 0;
        for (int i = 0; i < split.size(); i++) {
            List<String> other = split.get(i);
            if (i != at && other.size() >= depth
                    && other.subList(other.size() - depth, other.size()).equals(tail)) {
                shared++;
            }
        }
        return shared;
    }

    /** A path's segments, on either separator — a caller may have written the path by hand. */
    private static List<String> segmentsOf(String path) {
        List<String> segments = new ArrayList<>();
        for (String segment : path.split("[/\\\\]")) {
            if (!segment.isEmpty()) {
                segments.add(segment);
            }
        }
        return segments.isEmpty() ? List.of(path) : segments;
    }
}
