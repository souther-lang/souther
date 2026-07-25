CREATE TABLE IF NOT EXISTS issues (
    id       VARCHAR(64) PRIMARY KEY,
    title    VARCHAR(256) NOT NULL,
    assignee VARCHAR(64)
);

-- One row per label. The Set<Label> of an issue is these rows; storeLabels replaces them wholesale.
CREATE TABLE IF NOT EXISTS issue_labels (
    issue_id VARCHAR(64) NOT NULL,
    label    VARCHAR(64) NOT NULL,
    PRIMARY KEY (issue_id, label)
);
