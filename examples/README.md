# Souther examples

These examples exercise the whole Souther development lifecycle — write `.sou`, generate, use the
generated types from typed code, compile and test. Each business unit is an independent Maven
module: it generates types from its `.sou`, uses them from typed code, and runs a smoke test over
decode/encode.

A domain definition is just **data + invariant + behavior**. Decoders and encoders are not part of
the Souther notation; they are **derived** from the data shape (JSON key = field name; a data with a
single primitive field is a newtype = the bare primitive; the discriminator field of a sum is
`"type"` and the tag is the case name).

## How generation works: a javac annotation processor

`.sou → .class` is done not by a dedicated build-tool plugin but by a **javac annotation processor**
(`souther.compiler.apt.SoutherProcessor`). Whenever `mvn compile` (or plain javac, or
Gradle) runs, the processor compiles the `.sou` files in `src/main/souther` and emits the generated
types into `target/classes`. Because `target/classes` is on javac's compile classpath, the
hand-written code (and the smoke tests) **compile directly against those generated types**. No exec
step, no separate module, no Souther-specific plugin.

The whole Maven wiring is just this (set once for all modules in `examples/pom.xml`):

```xml
<plugin>
  <artifactId>maven-compiler-plugin</artifactId>
  <configuration>
    <annotationProcessorPaths>
      <path>org.souther-lang:souther-compiler:0.1.0-SNAPSHOT</path>
    </annotationProcessorPaths>
    <compilerArgs><arg>-Asouther.source=${project.basedir}/src/main/souther</arg></compilerArgs>
  </configuration>
</plugin>
```

`souther-compiler` only sits on `annotationProcessorPaths`; it is not an app dependency and does not
end up in the artifact jar. With Gradle you use the same processor via an `annotationProcessor`
dependency plus the `-Asouther.source` compiler arg.

## Modules

| Module | What it shows |
| --- | --- |
| `email` | A single-field data + invariant (the minimal example: a newtype decoded from a bare string) |
| `contact` | A sum data (sealed) + a discriminated decoder (discriminator `"type"`, tag = case name) |
| `expense` | `List<T>` / nested newtypes / a product decode·encode round trip |
| `cart` | List combinators `map`/`filter`/`all`/`any` (`souther.list` derives them from `fold`) + the empty list `[]`. Actually runs the behavior `quote` and checks its result cases |
| `businesstrip` | include (field composition) + a nested newtype invariant |
| `issuetracker` | A small issue tracker, and the **Kotlin** case: the boundary around the domain — REST and the H2 connection — is Spring Boot + Kotlin (below). Showcases the `Set` module (an issue's `labels` are a `Set<Label>` — the derived codec dedups a JSON array), the `Map` module (`countByLabel` builds a `Map<String, Int>` with `Map.upsert`), `Some(Assignee(name))` destructuring of an optional assignee, and three injected database behaviors whose read → transform → write sequencing is checked with `fake` + `example`. Like ordering it actually starts Boot and connects to H2 |
| `member` | Member lookup. A `required behavior findMember` (outside-world dependency) + type routing `>->`. Actually compiles the Spring MVC + jOOQ boundary code (below) |
| `account` | Account withdrawal, "read → check → write". Binds `withdraw` (which has two injected behaviors) from **Clojure + Pedestal rather than Java**, connected to H2 inside a transaction (below). It shows that the generated types are used the same way even when the boundary language changes |
| `ordering` | Ordering + stock reservation. Two injected behaviors joined with `>->`, and it **actually starts Spring Boot, connects to H2, and shows transaction control**: if the second stage returns the `OutOfStock` case, the first stage's INSERT is rolled back too (below). Also a pure `report` over a recorded order — a sales summary showcasing `distinct` (the old standalone `sales` example, folded in here) |
| `inventory` | The warehouse side. A third Souther module living inside the ordering project alongside `cart` and `ordering` (so it `import`s cart's `PricedCart`): `allocate` (read → aggregate check → write — read stock, check every line is covered with `all`, then commit), EAN-13 `inspectBarcode` (a check-digit fold with `List.indexedMap` / `List.sum`), whole-case `verifyShipment`, and `putAway` |

Modules that are `.sou`-only with no hand-written Java (email/contact/expense/cart/businesstrip)
carry a single minimal `package-info.java` to trigger the processor (javac does not run annotation
processing unless there is at least one source). The smoke tests call the generated
`decoder()`/`encoder()` in a typed way (`decoder()` is `Decoder<…, T>`; `decode(input, Path.ROOT)`
returns `Result<T>`, and `Ok`/`Err` are told apart by pattern match — no wildcard, no cast).

## Running

```sh
mvn -o install -DskipTests              # core (souther-runtime / souther-compiler) into ~/.m2
mvn -o -f examples/pom.xml verify       # generate → compile → smoke-test every example (except account, which is Clojure — below)
```

This is kept independent of the core reactor (the root `mvn test`) so the Spring/jOOQ dependencies
do not weigh the core build down.

`ordering` and `issuetracker` actually start Spring Boot, and `issuetracker` also needs the Kotlin
compiler, so **the first build needs network to fetch the starters and kotlin-maven-plugin** (run it
once without `-o` and it lands in `~/.m2`; after that `-o` works). The other examples run offline.

## Java interop (Spring MVC + jOOQ) — member

The `member` module shows, in a typed way, how the generated types are used from a real app, and it
**actually compiles**. The flow is one-directional.

```text
HTTP → decode (Result<会員ID>) → behavior >-> → match the output cases → encode → HTTP
```

The gist of `member.sou`:

```text
behavior findMember : (id: 会員ID) -> 会員 | 会員なし | 保存データ不正    // no impl → injected from Java
behavior 会員を照会し整形する = findMember >-> 会員を表示用に整形する
// 会員を照会し整形する : 会員ID -> 会員表示 | 会員なし | 保存データ不正
```

Only `findMember`'s success case `会員` flows into the formatting stage; the two failure cases pass
through it and remain in the output (type routing, spec 14.2). The required set `{findMember}` is
inferred by the compiler. The output is **domain outcomes only** — a platform failure such as a DB
outage is not a case: the Java binding throws and Souther passes it through (spec 13.4 / ADR-0029).

The generated `findMember` is an **abstract base class** (it implements `Behavior`) that carries
`protected` factories for the declared unit-data output cases `会員なし` / `保存データ不正`. The
implementation `extends` it and builds the failure cases with the inherited factories (not `new`).

| Java file | Package | Role |
| --- | --- | --- |
| `JooqFindMember.java` | `app.member` | The jOOQ impl that **extends** `findMember`. The success value `会員` is built with the decoder; the failure cases with the inherited `会員なし()` / `保存データ不正()`. DB exceptions are not caught — they are thrown (platform failures pass through) |
| `SoutherBeans.java` | `app.member.web` | Binds the pipeline with `会員を照会し整形する.bind(new JooqFindMember(dsl))` and exposes it as a Bean (spec 19.5) |
| `MemberController.java` | `app.member.web` | `@RestController`. Decodes input with `会員ID.decoder()` (branching on `Result`'s `Ok`/`Err`), folds the domain output cases into an HTTP status (200 / 404 / 500) with a `switch`. A platform-failure exception that passed through is mapped to 503 by an `@ExceptionHandler`. encode returns a plain Map, so Spring/Jackson serialize it to JSON as-is |

The generated-path containment (spec 2.1) holds even across the Java boundary. Because data
constructors are non-public, the controller cannot build data — it only tells the output cases apart
by type and encodes them. Only the effect implementation (`JooqFindMember`) can construct, and only
the cases **the behavior it extends declared**. `new 会員なし()` from another package will not
compile. Reading values out also goes through the encoder (spec 8.5).

> `MemberController`'s `@ExceptionHandler` catches Spring's `org.springframework.dao.DataAccessException`
> and maps it to 503 (the boundary type of ADR-0029). jOOQ's own exceptions are not subclasses of
> that type, so the injected `DSLContext` must have Spring's exception translation enabled (Spring
> Boot's jOOQ auto-config adds it by default; `ordering` verifies a real 503 through this path).

## Spring Boot + H2 + transaction control — ordering

Unlike member, `ordering` does not just **compile** the boundary code — it **actually starts Spring
Boot, connects to H2, and verifies transaction control**. The test brings up embedded Tomcat with
`@SpringBootTest(webEnvironment = RANDOM_PORT)` and sends **real HTTP** (the JDK `HttpClient`) to
`POST /orders` — Tomcat → Jackson → controller → service → transaction → H2 → JSON. Where the other
examples keep external dependencies `provided` (never run), this one resolves the Spring Boot 4
starters at real versions and runs them (DataSource / DSLContext / TransactionManager / schema.sql
execution are all left to autoconfig).

The pipeline joins two injected behaviors with `>->`. **The output is domain outcomes only** — it
has no infra case such as "DB unreachable":

```text
behavior 注文を記録する   : (注文: 注文) -> 注文受付              // INSERT orders (injected)
behavior 在庫を引き当てる : (受付: 注文受付) -> 注文確定 | 在庫不足  // UPDATE stock (injected)
behavior 注文を処理する = 注文を記録する >-> 在庫を引き当てる
// 注文を処理する : 注文 -> 注文確定 | 在庫不足
```

The first stage `注文を記録する`'s success case `注文受付` matches the second stage's input type and
flows in (type routing, spec 14.2). The highlight is that **rollback happens in two ways**.

**A domain failure (out of stock) → rolled back programmatically.** Because Souther represents
failure as a **case rather than an exception**, `在庫不足` arrives as a "returned value", not a
"thrown exception". The controller runs the pipeline inside a `TransactionTemplate`, `switch`es on
the output case, and for `在庫不足` calls **`setRollbackOnly()`** (the same switch also decides the
HTTP status). The order row the first stage INSERTed is rolled back by this.

**A platform failure (DB down, etc.) → auto-rolled-back by exception.** This is not a domain
outcome, so it is not a case. The Java binding (the jOOQ impl) throws, and **Souther passes it
through** (the generated `>->` pipeline does not swallow exceptions). `TransactionTemplate`
auto-rolls-back on the RuntimeException, and the boundary's `@ExceptionHandler` maps it to 503. "The
language has no exceptions, but the boundary Java throws; the distinction is domain outcome vs
platform failure" — that is the policy of spec §13.4 / ADR-0029, and this example demonstrates it.

| Java file | Package | Role |
| --- | --- | --- |
| `JooqRecordOrder.java` | `app.ordering` | The jOOQ impl that **extends** `注文を記録する`. INSERTs into orders and builds the assigned `注文受付` with the decoder. DB exceptions are not caught — they are thrown (platform failures pass through) |
| `JooqAllocateStock.java` | `app.ordering` | Extends `在庫を引き当てる`. Reserves stock with a conditional UPDATE; if zero rows change, the inherited `在庫不足()`. On confirmation the remaining stock is read as a jOOQ `Record` and built with **`注文確定.recordDecoder()`** (raoh-jooq's Record-source decoder, spec 10.6). DB exceptions are thrown |
| `OrderingConfig.java` | `app.ordering.web` | Adds only the generated-side beans: the injected impls, `注文を処理する.bind(...)`, `TransactionTemplate`, and a `Settings` that turns off jOOQ identifier quoting (unquoted names are upper-cased by H2, so they match the lower-case table names in code). DataSource / DSLContext / TransactionManager come from autoconfig. The autoconfig DSLContext goes through a `TransactionAwareDataSourceProxy`, so the first stage's INSERT and the second stage's UPDATE join one transaction (the premise for rollback) |
| `OrderController.java` | `app.ordering.web` | `@RestController` + transaction control. Decodes the body with `注文.decoder()` (destructuring `Ok` with a record pattern, `Err` is 400) and runs the pipeline inside `TransactionTemplate.execute`. One `switch` folds the output cases into an HTTP status (confirmed 201 / out of stock 409) and also calls `setRollbackOnly()` for `在庫不足`. A platform-failure exception that passed through is mapped to 503 by an `@ExceptionHandler` |

The test `OrderingTransactionTest` verifies both rollbacks against a real DB — the 409 for out of
stock, and a **503 for a platform failure** triggered by dropping the stock table — and that in both
cases **no order row remains in the DB** (the first stage's INSERT was rolled back). That is the
evidence of transaction control. As with member, the generated-path containment (spec 2.1) holds
across the Java boundary, and reading values out goes through the encoder (spec 8.5).

> This example and `issuetracker` fetch the Spring Boot starters on the first build, so **they need
> network** (the others run offline). Once they are in `~/.m2`, `-o` works after that. The DB
> connection info is in `src/main/resources/application.properties` (in-memory H2), and the schema and
> stock seed are in `schema.sql` / `data.sql`, both loaded at startup by Boot's autoconfig.

## Kotlin + Spring Boot interop — issuetracker

`issuetracker` is the same arrangement as ordering with the boundary language changed: `issues.sou` is
the domain, and everything outside it — the REST routes and the H2 connection — is Kotlin. It starts
Boot and drives every route over real HTTP against H2 in its tests.

The domain has three injected behaviors and three composed ones. The label operations are read →
transform → write, so their sequencing is checked at compile time with the database faked:

```text
behavior findIssue   : (id: IssueId) -> Issue | IssueNotFound   // SELECT (injected)
behavior createIssue : (issue: Issue) -> Issue                  // INSERT (injected)
behavior storeLabels : (issue: Issue) -> Issue                  // rewrite the label rows (injected)

behavior openIssue   : (draft: NewIssue) -> Issue | NoLabels        requires createIssue
behavior attachLabel : (request: LabelRequest) -> Issue | IssueNotFound  requires findIssue, storeLabels
behavior detachLabel : (request: LabelRequest) -> Issue | IssueNotFound  requires findIssue, storeLabels
```

`attachLabel` reads the issue, inserts into its label `Set` and writes it back; an unknown id passes
`IssueNotFound` through without writing. The remaining behaviors (`assigneeOf`, `sharedLabels`,
`countByLabel`, `topLabels`) are pure, so they need no injection, and each one has a route.

### Making a javac annotation processor work in a Kotlin module

Souther generates through a javac annotation processor, and kotlinc is not javac — so the module needs
an order: javac (with `SoutherProcessor`, over the one `package-info.java`) emits the generated classes
into `target/classes`, and only then does kotlinc run, with `target/classes` on its compile classpath.
Both plugins bind to the `compile` phase, and the parent pom declares maven-compiler-plugin while the
module declares kotlin-maven-plugin, so the effective order is javac first. This is the reverse of the
usual mixed Kotlin/Java setup, where kotlinc is pulled forward to `process-sources`; here nothing on
the Java side depends on Kotlin, and everything on the Kotlin side depends on generated bytecode.

Two details the module pins down: `kotlin.version` is declared as a property rather than taken from
the imported `spring-boot-dependencies` BOM (a BOM property does not reach a plugin version), and
`jvmTarget` is set, because kotlinc still defaults to a 1.8 target.

### What Kotlin brings to the boundary

An output union is generated as a Java `sealed` interface, so `when` over it is exhaustive and the
compiler names the missing case. That is Souther's `match` totality carried across the boundary as a
language feature — the thing account's `case-of` macro had to hand-build for Clojure, and that Java
gets from a `switch` expression.

Souther's `Option` is a sealed interface too, so it maps onto Kotlin's own nullability in one
extension (`orNull()`), and the rest of the boundary uses `?.` and `?:`.

A request body arrives as a plain `Map` and is handed to the derived decoder — there is no Kotlin
data class mirroring the request shape. The shape is already declared in `issues.sou`, and the decoder
is what checks the invariants and reports failures as Raoh issues with their JSON paths. A data class
would duplicate the domain shape and would reject a malformed body in Jackson, before the decoder that
holds the actual rules ever ran. So the module has no `jackson-module-kotlin` dependency: no request
or response shape is a Kotlin type.

The whole Kotlin-side glue is one file, `souther/Souther.kt`: an exception type, `decodeOrFail`,
`orNull`, and an `operator invoke` so a bound behavior is called as `attachLabel(request)` rather than
`attachLabel.apply(request)`. It names no domain type and is written to be lifted out unchanged, the
same way `souther-clj` was.

| Kotlin file | Role |
| --- | --- |
| `souther/Souther.kt` | The boundary glue, naming no domain type: `DecodeFailed`, `decodeOrFail` (decode or fail the request), `Option.orNull()`, and `operator invoke` for `Behavior` |
| `IssueRows.kt` | The one place that knows the issue tables. An issue spans `issues` and its `issue_labels` rows, so reading one produces the Map `Issue.decoder()` takes (labels as a list → a `Set` on decode; an absent assignee left out of the Map → `None`). Reading values out of a domain value is plain typed accessor access — construction is the guarded direction, not reading |
| `JooqIssueStore.kt` | The three injected implementations, each **extending** the generated abstract base. A Kotlin subclass reaches the base's `protected` factories, so the unit case is built with the inherited `IssueNotFound()`; values read out of storage go through the public `decoder()`, which re-checks their invariants. SQL exceptions are not caught |
| `web/IssueTrackerConfig.kt` | The generated-side beans: the injected implementations, `AttachLabel.bind(...)` and friends, the pure behaviors' `of()`, and a jOOQ `Settings` that turns identifier quoting off. DataSource / DSLContext / TransactionManager come from autoconfig |
| `web/IssueController.kt` | `@RestController`. Every route is decode → one behavior → fold the output union into a status and a body. `@Transactional` on the read-modify-write routes, so a concurrent call cannot drop a label by writing back a set it read too early |
| `web/BoardQuery.kt` | The read side. `countByLabel` / `topLabels` are pure behaviors over a whole `Board`, and a summary makes no decision the domain needs to be in on, so this is not an injected behavior: the boundary reads the rows and builds the `Board` through the derived decoder |
| `web/BoundaryErrors.kt` | The two failures that are not domain outcomes: a rejected input is 400 with Raoh's issues, and a `DataAccessException` that passed through Souther is 503 |

| Route | Behavior | Outcomes |
| --- | --- | --- |
| `POST /issues` | `openIssue` | 201 with the stored issue / 400 `no_labels` when the raw label text leaves nothing |
| `GET /issues/{id}` | `findIssue` | 200 / 404 |
| `GET /issues/{id}/assignee` | `assigneeOf` | 200 with the name / 204 when unassigned |
| `POST /issues/{id}/labels` | `attachLabel` | 200 with the issue / 404 |
| `DELETE /issues/{id}/labels/{label}` | `detachLabel` | 200 with the issue / 404 |
| `GET /issues/{a}/shared-labels/{b}` | `sharedLabels` | 200 with the intersection / 404 |
| `GET /labels/counts` | `countByLabel` | 200 with a JSON object of label → count |
| `GET /labels/top?n=` | `topLabels` | 200 with the ranking |

`IssueTrackerApiTest` boots Tomcat on a random port and drives all of these over real HTTP with
`RestTestClient`, checking the three failure kinds apart from each other: `NoLabels` is a domain
outcome and arrives as a returned case (400 `no_labels`), an empty `label` is an invariant violation
the decoder rejects before any behavior runs (400, with `/label` as the issue's path), and a dropped
table is no case at all — it passes through Souther as an exception and becomes 503.

### Running

```sh
mvn -o -f examples/pom.xml -pl issuetracker verify   # generate → kotlinc → boot → real HTTP over H2
mvn -f examples/issuetracker/pom.xml spring-boot:run # starts on localhost:8080
```

```sh
curl localhost:8080/issues/i-1
# {"id":"i-1","title":"crash on save","labels":["bug","ui"],"assignee":"kawasima"}
curl -X POST localhost:8080/issues/i-2/labels \
     -H 'Content-Type: application/json' -d '{"label":"ui"}'      # 200, i-2 now carries bug and ui
curl -X POST localhost:8080/issues \
     -H 'Content-Type: application/json' \
     -d '{"id":"i-3","title":"flaky test","labels":"Bug, bug , UI"}'  # 201, labels ["bug","ui"]
curl localhost:8080/labels/top?n=1                                    # {"labels":["bug"]}
```

## Clojure + Pedestal interop — account

`account` shows that the boundary using the generated types can be **Clojure rather than Java** and
nothing else changes. The domain is the same "read → check → write" as ordering, with two injected
behaviors. The output is **domain outcomes only**.

```text
behavior currentBalance : (account: AccountNo) -> Balance | NoAccount             // SELECT (injected)
behavior updateBalance  : (account: AccountNo, newBalance: Balance) -> Withdrawn   // UPDATE (injected)
behavior withdraw : (request: WithdrawRequest) -> Withdrawn | InsufficientFunds | NoAccount
    requires currentBalance, updateBalance
```

`withdraw`'s body reads the current balance, passes through if there is no account, otherwise checks
it with `require current.value >= request.amount.value`, and writes the new balance if funds are
enough. The non-negativity of the new balance `Balance(current - amount)` is discharged at compile
time by the require just above it. If funds are short it returns `InsufficientFunds` without writing.

The `.sou`-side compile-time check (`fake` + `example` confirm the three cases with no DB) runs
whenever `SoutherProcessor` generates the classes — here that is `clojure -X:gen` (account is a
Clojure/`deps.edn` project, not a Maven reactor module). The account module has no hand-written Java,
so it carries a single minimal `package-info.java` to trigger the processor. **The Clojure app puts
that generated output (`target/classes`) straight on its classpath** (`target/classes` is in
`:paths` in `deps.edn`).

### Implementing an injected behavior from Clojure — `proxy` + `decoder()`

The generated injected behaviors are **abstract base classes** (`CurrentBalance` implements
`Behavior<AccountNo, CurrentBalanceResult>`; `UpdateBalance` has `apply(AccountNo, Balance)`).
Clojure implements them with `proxy`. But a `proxy` cannot reach the base's `protected` factories,
so it builds the returned domain values (`Balance` / `Withdrawn` / `NoAccount`) through the
**public generated `decoder()`** — the sanctioned boundary path for turning outside values into
domain data, with data constructors staying non-public (spec 8.5 / 2.1). No gen-class, no AOT.

These interop patterns are packaged as a small reusable library under `souther-clj/` (see its
README), written to be lifted out into its own repo unchanged — its source refers to no domain
type and works by reflection over whatever generated classes the caller passes in:

- `souther.decode` — `decode` runs a `decoder()` over Clojure data (keyword keys accepted) and
  returns `[:ok value]` / `[:err issues]` with issues as plain maps; `construct` builds a case value
  through its `decoder()`.
- `souther.encode` — the inverse: `encode` runs a value's `encoder()` and returns Clojure data,
  unwrapping newtypes (a newtype → its bare value, a record → a keyword map with nested newtypes
  already unwrapped); `unwrap` is that narrowed to a single wrapper. No chains of `.value`.
- `souther.behavior` — `defbehavior`, the `proxy` sugar for an injected behavior; `as-fn`, which
  turns a bound behavior into a plain Clojure fn (called `(f input)`, not `(.apply b input)`).
- `souther.match` — `case-of`, which folds a sealed output union and checks **at macro-expansion**
  that the handlers cover exactly the union's permitted subclasses — carrying Souther's `match`
  totality across the boundary (drop a case and it is a compile error, not a silent fall-through).

| Clojure file | Role |
| --- | --- |
| `account/db.clj` | The H2 DataSource, schema, and seed. The dynamic var `*conn*` is the seam that binds "read → check → write" into one transaction: the boundary rebinds it to the transaction's connection, and both behaviors query through `current`, so `currentBalance`'s SELECT and `updateBalance`'s UPDATE join the same connection |
| `account/behaviors.clj` | Implements `currentBalance` / `updateBalance` with `souther.behavior/defbehavior`, building the return values with `souther.decode/construct` and reading newtype arguments with `souther.encode/unwrap` (no `.value`). Exposes `withdraw-fn` / `current-balance-fn` — the bound behaviors as plain Clojure fns via `souther.behavior/as-fn`. SQL exceptions are not caught — they are thrown (platform failures pass through) |
| `account/service.clj` | The Pedestal boundary. The whole request is the JSON body `{"account": …, "amount": …}`, handed straight to `WithdrawRequest/decoder` via `souther.decode/decode` (the `Amount` invariant `value >= 0` is rejected here → 400, and the Raoh issues are returned in the body). Then it calls `withdraw` (a fn) inside `with-transaction`, folds the output with `souther.match/case-of` (miss a case and it will not compile), and `souther.encode/encode`s the result value to the JSON body — Withdrawn 200 `{account, newBalance}` / InsufficientFunds 409 / NoAccount 404 |
| `account/server.clj` | The `-main` that creates and seeds H2 and starts Jetty |

`InsufficientFunds` / `NoAccount` arrive as **returned values**, and no write happened on those
branches, so there is nothing to roll back. Wrapping read → check → write in one transaction is for
atomicity — so a concurrent withdrawal cannot interleave and double-spend. A platform failure (a SQL
exception) is not a case: it passes through `withdraw` untouched, `with-transaction` auto-rolls-back,
and it propagates to the framework. The full platform-failure → 503 + rollback treatment against a
real DB is shown by `ordering`, so account does not repeat it.

### Running

Generate the types first, then run Clojure (Clojure lives outside the Maven reactor, in its own
`deps.edn`). Generation itself needs no Maven — the `:gen` alias runs `SoutherProcessor` through the
JDK compiler API (`souther.build/generate!`), with `souther-compiler` on the alias classpath only:

```sh
cd examples/account
clojure -X:gen                                   # .sou → target/classes (the .sou examples are checked here too)
clojure -X:test                                  # the souther-clj library, behavior+DB, and Pedestal boundary tests (20 of them)
clojure -M:run                                   # starts on localhost:8890
```

`clojure -X:gen` is the only generation path for account: unlike the other examples it is not a
Maven reactor module, so `mvn … verify` does not build it — its `.sou` is checked by the `:gen` run
above.

```sh
curl localhost:8890/accounts/acc-1                                            # {"account":"acc-1","balance":1000}
curl -X POST localhost:8890/withdrawals \
     -H 'Content-Type: application/json' -d '{"account":"acc-1","amount":300}'  # {"account":"acc-1","newBalance":700}
curl -X POST localhost:8890/withdrawals \
     -H 'Content-Type: application/json' -d '{"account":"acc-1","amount":5000}' # 409 {"error":"insufficient_funds","shortfall":...}
```

> Clojure / Pedestal / next.jdbc are fetched from clojars / Central on the first run, so **it needs
> network** (once they are in `~/.m2` and gitlibs, no more). `mvn -o -f examples/pom.xml verify` does
> not include this Clojure app (a separate toolchain). The account module itself is generated and
> checked offline, like the others.
