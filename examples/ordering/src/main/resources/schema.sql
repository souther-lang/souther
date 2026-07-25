CREATE TABLE IF NOT EXISTS orders (
    id    VARCHAR(64) PRIMARY KEY,
    total INT         NOT NULL
);

CREATE TABLE IF NOT EXISTS order_lines (
    order_id   VARCHAR(64) NOT NULL,
    sku        VARCHAR(64) NOT NULL,
    qty        INT         NOT NULL,
    unit_price INT         NOT NULL
);

CREATE TABLE IF NOT EXISTS stock (
    sku VARCHAR(64) PRIMARY KEY,
    qty INT         NOT NULL
);

-- The rate in force for each tax category. NUMERIC, because a rate is not an integer — it is the one
-- column in this schema that arrives in the domain as a Decimal.
CREATE TABLE IF NOT EXISTS tax_rates (
    category VARCHAR(32)  PRIMARY KEY,
    rate     NUMERIC(4,3) NOT NULL
);

MERGE INTO tax_rates (category, rate) KEY (category) VALUES ('StandardRate', 0.100);
MERGE INTO tax_rates (category, rate) KEY (category) VALUES ('ReducedRate',  0.080);
