use nasrudin_rocks::{ReverifyJob, TheoremDb};
use tempfile::tempdir;

#[test]
fn enqueue_and_drain_round_trip() {
    let dir = tempdir().unwrap();
    let db = TheoremDb::new(dir.path().to_str().unwrap()).unwrap();
    let job = ReverifyJob {
        theorem_id: [1, 2, 3, 4, 5, 6, 7, 8],
        attempts: 0,
        enqueued_at_micros: 1700000000_000_000,
    };
    db.enqueue_reverify(&job).unwrap();
    let pending = db.list_reverify_pending(10).unwrap();
    assert_eq!(pending.len(), 1);
    assert_eq!(pending[0].theorem_id, job.theorem_id);
    assert_eq!(pending[0].attempts, 0);
    assert_eq!(pending[0].enqueued_at_micros, 1700000000_000_000);
    db.dequeue_reverify(&job.theorem_id).unwrap();
    let pending = db.list_reverify_pending(10).unwrap();
    assert!(pending.is_empty());
}

#[test]
fn queue_persists_across_reopen() {
    let dir = tempdir().unwrap();
    {
        let db = TheoremDb::new(dir.path().to_str().unwrap()).unwrap();
        db.enqueue_reverify(&ReverifyJob {
            theorem_id: [9; 8],
            attempts: 0,
            enqueued_at_micros: 0,
        })
        .unwrap();
    }
    let db = TheoremDb::new(dir.path().to_str().unwrap()).unwrap();
    let pending = db.list_reverify_pending(10).unwrap();
    assert_eq!(pending.len(), 1);
    assert_eq!(pending[0].theorem_id, [9; 8]);
}

#[test]
fn list_respects_limit() {
    let dir = tempdir().unwrap();
    let db = TheoremDb::new(dir.path().to_str().unwrap()).unwrap();
    for i in 0u8..20 {
        db.enqueue_reverify(&ReverifyJob {
            theorem_id: [i; 8],
            attempts: 0,
            enqueued_at_micros: 0,
        })
        .unwrap();
    }
    let pending = db.list_reverify_pending(5).unwrap();
    assert_eq!(pending.len(), 5);
}

#[test]
fn queue_depth_reports_correct_count() {
    let dir = tempdir().unwrap();
    let db = TheoremDb::new(dir.path().to_str().unwrap()).unwrap();
    assert_eq!(db.reverify_queue_depth().unwrap(), 0);
    for i in 0u8..7 {
        db.enqueue_reverify(&ReverifyJob {
            theorem_id: [i; 8],
            attempts: 0,
            enqueued_at_micros: 0,
        })
        .unwrap();
    }
    assert_eq!(db.reverify_queue_depth().unwrap(), 7);
    db.dequeue_reverify(&[3; 8]).unwrap();
    assert_eq!(db.reverify_queue_depth().unwrap(), 6);
}
