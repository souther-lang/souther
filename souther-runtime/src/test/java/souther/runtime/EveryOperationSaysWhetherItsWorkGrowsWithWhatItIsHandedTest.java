package souther.runtime;

import org.junit.jupiter.api.Test;
import souther.test.ClosedWorldContract;

import java.io.IOException;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.net.URISyntaxException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Every public static of this runtime either has an entry taking a {@link WorkCheckpoint} last, or
 * is named below as one whose work does not grow with what it is handed, and says why.
 *
 * <p>The entry taking a checkpoint is what an evaluated class calls, and the compiler's sweep over
 * the classes it generates holds it to calling that entry wherever there is one. What that sweep
 * cannot see is an operation that should have one and does not, so this is the other half: an
 * operation added later is in neither place until somebody says which it is.
 */
@ClosedWorldContract
class EveryOperationSaysWhetherItsWorkGrowsWithWhatItIsHandedTest {

    /** The operations whose work is bounded by a constant whatever they are handed, by
     *  {@code Class.method(parameter types)}, and why. */
    private static final Map<String, String> FIXED = new TreeMap<>();

    /** The operations that spell a value out for a person reading a message, which no operation of
     *  the language asks for, and why that is so. */
    private static final Map<String, String> FOR_A_READER = new TreeMap<>();

    static {
        String whole = "arithmetic on two whole numbers held in sixty-four bits";
        for (String each : List.of("addExact", "compare", "divideExact", "floorMod", "multiplyExact",
                "subtractExact")) {
            FIXED.put("IntMath." + each + "(long, long)", whole);
        }
        FIXED.put("IntMath.negateExact(long)", whole);
        String time = "a field of a date or a time, or a shift of one, which java.time works out from fields";
        for (String each : List.of("Temporals.addDateTimeDays(LocalDateTime, long)",
                "Temporals.addDays(LocalDate, long)", "Temporals.addHours(LocalDateTime, long)",
                "Temporals.addMinutes(LocalDateTime, long)", "Temporals.addMonths(LocalDate, long)",
                "Temporals.addYears(LocalDate, long)", "Temporals.day(LocalDate)",
                "Temporals.daysBetween(LocalDate, LocalDate)", "Temporals.fromDateParts(long, long, long)",
                "Temporals.fromTimeParts(long, long, long)", "Temporals.hour(LocalTime)",
                "Temporals.minute(LocalTime)", "Temporals.minutesBetween(LocalDateTime, LocalDateTime)",
                "Temporals.month(LocalDate)", "Temporals.second(LocalTime)", "Temporals.year(LocalDate)",
                "Temporals.toTheSecond(Object)")) {
            FIXED.put(each, time);
        }
        String size = "a size a collection keeps, read";
        FIXED.put("Lists.length(List)", size);
        FIXED.put("Maps.isEmpty(Map)", size);
        FIXED.put("Maps.size(Map)", size);
        FIXED.put("Sets.isEmpty(Set)", size);
        FIXED.put("Sets.size(Set)", size);
        FIXED.put("Lists.get(List, long)", "a step of a trie as deep as an index's bits");
        String empty = "the empty collection there is one of";
        FIXED.put("Maps.empty()", empty);
        FIXED.put("Sets.empty()", empty);
        FIXED.put("PersistentHashMap.empty()", empty);
        FIXED.put("PersistentHashSet.empty()", empty);
        FIXED.put("PersistentVector.empty()", empty);
        FIXED.put("PersistentVector.ofSingle(Object)", "one element put in, which compares nothing");
        String builder = "a builder made, added to or sealed: one element, compared with nothing";
        FIXED.put("Lists.builder()", builder);
        FIXED.put("Lists.grow(List, Object)", builder);
        FIXED.put("Lists.sealed(List)", builder);
        FIXED.put("Maps.sealed(Map)", builder);
        FIXED.put("Maps.put(Map, Object, Object)",
                "one entry written into a builder, whose keys are compared under the checkpoint the"
                        + " builder was made with");
        String once = "the function applied to the one value an option holds, which counts what it does itself";
        FIXED.put("Options.map(Fn, Option)", once);
        FIXED.put("Options.mapWith(Function, Option)", once);
        FIXED.put("Options.encodedOrNull(Function, Option)", once);
        String made = "a value made of what it is handed, compared with nothing";
        FIXED.put("Option.none()", made);
        FIXED.put("Option.ofNullable(Object)", made);
        FIXED.put("Option.some(Object)", made);
        FIXED.put("Result.err(Object)", made);
        FIXED.put("Result.ok(Object)", made);
        FIXED.put("Tuple.of(Object, Object)", made);
        String arity = "a tuple of as many elements as the source writes";
        FIXED.put("Tuple.of(Object[])", arity);
        FIXED.put("Tuple.ofOwned(Object[])", arity);
        String number = "a number of sixty-four bits made into another kind of number";
        FIXED.put("DecimalMath.fromInt(long)", number);
        FIXED.put("RationalMath.fromInt(long)", number);
        FIXED.put("Rational.of(long)", number);
        FIXED.put("Strings.fromInt(long)", number);
        FIXED.put("RationalMath.divideWholeNumbers(long, long)",
                "the quotient of two whole numbers held in sixty-four bits, taken to lowest terms");
        FIXED.put("DecimalMath.toJava(RoundingMode)", "one case mapped to another");
        String order = "where a case of the rounding modes stands, read off the case";
        FIXED.put("RoundingMode.__order(Object)", order);
        FIXED.put("RoundingMode.__ordering()", order);
        FIXED.put("RoundingMode.__tag(Object)", order);
        String carrier = "which carrier arrived, and a scale read off it";
        FIXED.put("BoundaryScalars.decimalRefusal(Object)", carrier);
        FIXED.put("BoundaryScalars.intRefusal(Object)", carrier);
        String abort = "an abort that names what failed by the names the source wrote";
        FIXED.put("ConstraintViolation.notHeld(ConstraintFailure)", abort);
        FIXED.put("ConstraintViolation.orThrow(Result)", abort);
        FIXED.put("InvariantFailure.of(String, String, String)", abort);
        FIXED.put("InvariantFailure.unnamed(String, String)", abort);
        FIXED.put("UnreachableReached.reached(String)", abort);
        FIXED.put("Patterns.read(Lookup, String, Class, String[])",
                "a pattern's machine made once for a class, from the image the compiler wrote into it");

        FOR_A_READER.put("Tuple.show(Tuple)", "a tuple's toString, which writes what each element's"
                + " own toString writes; generated code asks for neither");
    }

    @Test
    void everyOperationHasAnEntryThatPassesACheckpointOrIsNamedAsFixed() throws IOException, URISyntaxException {
        TreeSet<String> unsaid = new TreeSet<>();
        TreeSet<String> stale = new TreeSet<>(FIXED.keySet());
        stale.addAll(FOR_A_READER.keySet());
        int read = 0;
        for (Class<?> each : runtimeClasses()) {
            for (Method m : each.getDeclaredMethods()) {
                if (!Modifier.isPublic(m.getModifiers()) || !Modifier.isStatic(m.getModifiers()) || m.isSynthetic()) {
                    continue;
                }
                read++;
                if (passesACheckpoint(m) || hasAnEntryThatPasses(each, m)) {
                    continue;
                }
                String key = key(m);
                stale.remove(key);
                if (!FIXED.containsKey(key) && !FOR_A_READER.containsKey(key)) {
                    unsaid.add(key);
                }
            }
        }
        assertEquals(List.of(), List.copyOf(unsaid), "operations that say neither");
        assertEquals(List.of(), List.copyOf(stale), "named as fixed, and no such operation");
        assertTrue(read > 100, "the runtime's operations were read: " + read);
    }

    private static boolean passesACheckpoint(Method m) {
        Class<?>[] takes = m.getParameterTypes();
        return takes.length > 0 && takes[takes.length - 1] == WorkCheckpoint.class;
    }

    private static boolean hasAnEntryThatPasses(Class<?> owner, Method m) {
        Class<?>[] counted = Arrays.copyOf(m.getParameterTypes(), m.getParameterCount() + 1);
        counted[m.getParameterCount()] = WorkCheckpoint.class;
        for (Method other : owner.getDeclaredMethods()) {
            if (other.getName().equals(m.getName()) && Arrays.equals(other.getParameterTypes(), counted)
                    && Modifier.isPublic(other.getModifiers()) && Modifier.isStatic(other.getModifiers())) {
                return true;
            }
        }
        return false;
    }

    private static String key(Method m) {
        StringBuilder out = new StringBuilder(m.getDeclaringClass().getSimpleName()).append('.')
                .append(m.getName()).append('(');
        Class<?>[] takes = m.getParameterTypes();
        for (int i = 0; i < takes.length; i++) {
            out.append(i == 0 ? "" : ", ").append(takes[i].getSimpleName());
        }
        return out.append(')').toString();
    }

    /** Every class of the package as compiled, nested ones included. */
    private static List<Class<?>> runtimeClasses() throws IOException, URISyntaxException {
        Path root = Path.of(Strings.class.getProtectionDomain().getCodeSource().getLocation().toURI())
                .resolve("souther").resolve("runtime");
        List<Class<?>> out = new ArrayList<>();
        try (Stream<Path> files = Files.list(root)) {
            for (Path file : files.sorted().toList()) {
                String name = file.getFileName().toString();
                if (name.endsWith(".class") && !name.equals("package-info.class")) {
                    try {
                        out.add(Class.forName("souther.runtime." + name.substring(0, name.length() - 6)));
                    } catch (ClassNotFoundException e) {
                        throw new IllegalStateException(e);
                    }
                }
            }
        }
        return out;
    }
}
