package souther.compiler.core;

/**
 * A kernel of the standard library: an operation the language names, and which every output answers
 * with instructions of its own.
 *
 * <p>What a core module declares as {@code intrinsic "string.trim"}, held as the operation rather
 * than as the spelling of it. The written key is how a declaration names one and what a report
 * quotes; it is not what tells two apart.
 *
 * <p>Reading a key back as a kernel is not something this can do. Turning a written key into the
 * operation it names is the library's, done where the library is frozen
 * ({@code stdlib.Stdlib.Builder#freeze}), and a kernel that could hand back the way it was made
 * would be that route open to everything downstream — which is the thing being closed. What this
 * publishes is the identity and the key a declaration or a report writes it as.
 *
 * <p>Closed, and that is not a limitation of what the library may declare. Which kernels there are
 * is a decision of the language rather than an extension point: an output that met one it had never
 * heard of could not emit it, so nothing is gained by being able to carry it. A reader switches over
 * these and javac says which arms it has not answered.
 *
 * <p>What a kernel is on some machine is not stated here. {@code string.trim} names an operation;
 * what instructions answer it is whichever output is emitting, exactly as {@code codegen.Intrinsics}
 * is the JVM's answer and no part of the language.
 *
 * <p>In {@code Reserved.MODULES} order, and inside a module in the order that module declares them,
 * so this list and the sources read alongside each other.
 */
public enum Kernel {

    // string
    STRING_LENGTH("string.length"),
    STRING_TO_INT("string.toInt"),
    STRING_TO_DECIMAL("string.toDecimal"),
    STRING_TRIM("string.trim"),
    STRING_LOWERCASE("string.lowercase"),
    STRING_UPPERCASE("string.uppercase"),
    STRING_CONTAINS("string.contains"),
    STRING_STARTS_WITH("string.startsWith"),
    STRING_ENDS_WITH("string.endsWith"),
    STRING_MATCHES("string.matches"),
    STRING_SLICE("string.slice"),
    STRING_APPEND("string.append"),
    STRING_SPLIT("string.split"),
    STRING_JOIN("string.join"),
    STRING_REPLACE("string.replace"),
    STRING_WORDS("string.words"),
    STRING_FROM_INT("string.fromInt"),
    STRING_CONCAT("string.concat"),
    STRING_REVERSE("string.reverse"),
    STRING_REPEAT("string.repeat"),
    STRING_LINES("string.lines"),
    STRING_PAD_LEFT("string.padLeft"),
    STRING_PAD_RIGHT("string.padRight"),
    STRING_FROM_DECIMAL("string.fromDecimal"),
    STRING_CHARACTERS("string.characters"),
    STRING_CODE_POINTS("string.codePoints"),
    // map
    MAP_EMPTY("map.empty"),
    MAP_GET("map.get"),
    MAP_CONTAINS_KEY("map.containsKey"),
    MAP_KEYS("map.keys"),
    MAP_VALUES("map.values"),
    MAP_SINGLETON("map.singleton"),
    MAP_INSERT("map.insert"),
    MAP_REMOVE("map.remove"),
    MAP_IS_EMPTY("map.isEmpty"),
    MAP_SIZE("map.size"),
    MAP_TO_LIST("map.toList"),
    MAP_FROM_LIST("map.fromList"),
    // list
    LIST_LENGTH("list.length"),
    LIST_FIND("list.find"),
    LIST_SORT_BY("list.sortBy"),
    LIST_MAX("list.max"),
    LIST_MIN("list.min"),
    LIST_GET("list.get"),
    LIST_REVERSE("list.reverse"),
    LIST_SUM("list.sum"),
    LIST_PRODUCT("list.product"),
    LIST_SORT("list.sort"),
    LIST_RANGE_INCLUSIVE("list.rangeInclusive"),
    // set
    SET_EMPTY("set.empty"),
    SET_SINGLETON("set.singleton"),
    SET_INSERT("set.insert"),
    SET_REMOVE("set.remove"),
    SET_CONTAINS("set.contains"),
    SET_UNION("set.union"),
    SET_INTERSECTION("set.intersection"),
    SET_DIFFERENCE("set.difference"),
    SET_IS_EMPTY("set.isEmpty"),
    SET_SIZE("set.size"),
    SET_TO_LIST("set.toList"),
    SET_FROM_LIST("set.fromList"),
    // date
    DATE_ADD_DAYS("date.addDays"),
    DATE_ADD_MONTHS("date.addMonths"),
    DATE_ADD_YEARS("date.addYears"),
    DATE_DAYS_BETWEEN("date.daysBetween"),
    DATE_YEAR("date.year"),
    DATE_MONTH("date.month"),
    DATE_DAY("date.day"),
    DATE_FROM_PARTS("date.fromParts"),
    // time
    TIME_FROM_PARTS("time.fromParts"),
    TIME_HOUR("time.hour"),
    TIME_MINUTE("time.minute"),
    TIME_SECOND("time.second"),
    // datetime
    DATETIME_ADD_MINUTES("datetime.addMinutes"),
    DATETIME_ADD_HOURS("datetime.addHours"),
    DATETIME_ADD_DAYS("datetime.addDays"),
    DATETIME_MINUTES_BETWEEN("datetime.minutesBetween"),
    DATETIME_TO_DATE("datetime.toDate"),
    DATETIME_TO_TIME("datetime.toTime"),
    DATETIME_FROM_DATE_AND_TIME("datetime.fromDateAndTime"),
    // int
    INT_DIVIDE("int.divide"),
    INT_TRUNCATING_REMAINDER("int.truncatingRemainder"),
    INT_ADD("int.add"),
    INT_SUBTRACT("int.subtract"),
    INT_MULTIPLY("int.multiply"),
    INT_COMPARE("int.compare"),
    INT_FLOOR_MOD("int.floorMod"),
    // decimal
    DECIMAL_DIVIDE("decimal.divide"),
    DECIMAL_TO_INT("decimal.toInt"),
    DECIMAL_ROUND("decimal.round"),
    DECIMAL_ADD("decimal.add"),
    DECIMAL_SUBTRACT("decimal.subtract"),
    DECIMAL_MULTIPLY("decimal.multiply"),
    DECIMAL_COMPARE("decimal.compare"),
    DECIMAL_FROM_INT("decimal.fromInt"),
    // option
    OPTION_MAP("option.map");

    private final String key;

    Kernel(String key) {
        this.key = key;
    }

    /** The key a declaration names this kernel by: {@code "string.trim"}. What a declaration is read
     *  through and what a report quotes — never how two kernels are told apart. */
    public String key() {
        return key;
    }
}
