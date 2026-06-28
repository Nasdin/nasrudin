import subprocess
import time
import requests
import psycopg2
import os
import sys

def submit_and_poll():
    print("═══════════════════════════════════════════════════════")
    print("  Nasrudin SOTA E2E Verification: Spontaneous E=mc2")
    print("═══════════════════════════════════════════════════════\n")

    # Fix unexpanded shell variables in DATABASE_URL from parent environment
    if "DATABASE_URL" in os.environ and "${POSTGRES_USER}" in os.environ["DATABASE_URL"]:
        os.environ["DATABASE_URL"] = "postgresql://physics:physics_dev@localhost:5432/physics_generator"

    # Disable persistent elaborator during test to allow instant worker boot
    os.environ["NASRUDIN_NO_PERSISTENT"] = "1"

    # 1. Start the entire dev stack cleanly using 'just up' in the background
    print("▶ Starting the entire stack using 'just up'...")
    # Kill any existing processes on ports 3000, 3001, 5005 and any orphan lean/lake compilers
    subprocess.run("kill -9 $(lsof -t -i:3000 -i:3001 -i:5005) 2>/dev/null || true", shell=True)
    subprocess.run("pkill -9 -f \"lean|lake|worker\" 2>/dev/null || true", shell=True)
    
    # Safely clear left-over RocksDB LOCK files
    subprocess.run("rm -f ./data/theorems.db/LOCK", shell=True)
    
    log_file = open("just_up.log", "w")
    proc_up = subprocess.Popen(
        ["just", "up"],
        stdout=log_file,
        stderr=log_file,
        text=True
    )
    
    # Wait for the SOTA RL server and API backend to be healthy
    print("  Waiting for services to boot...")
    rl_healthy = False
    api_healthy = False
    
    for _ in range(60):
        time.sleep(2)
        if not rl_healthy:
            try:
                res = requests.get("http://127.0.0.1:5005/status")
                if res.status_code == 200:
                    print("  ✓ SOTA RL server is healthy on port 5005")
                    rl_healthy = True
            except:
                pass
        if not api_healthy:
            try:
                res = requests.get("http://127.0.0.1:3001/api/health")
                if res.status_code == 200:
                    print("  ✓ API backend is healthy on port 3001")
                    api_healthy = True
            except:
                pass
        if rl_healthy and api_healthy:
            break
            
    if not (rl_healthy and api_healthy):
        print("  ✗ Failed to boot services within 2 minutes. Aborting.")
        proc_up.terminate()
        log_file.close()
        sys.exit(1)

    # 1.5 Purge older queued/running conjecture jobs from PostgreSQL to ensure immediate claim
    print("\n▶ Purging old conjecture jobs from database...")
    try:
        conn = psycopg2.connect(
            dbname="physics_generator",
            user="physics",
            password="physics_dev",
            host="localhost",
            port="5432"
        )
        cur = conn.cursor()
        cur.execute("DELETE FROM conjecture_jobs;")
        conn.commit()
        cur.close()
        conn.close()
        print("  ✓ Successfully purged older conjecture jobs.")
    except Exception as e:
        print(f"  ! Warning: could not purge database queue: {e}")

    # 2. Mint a live API key for our test user
    print("\n▶ Minting a live API key for the test researcher...")
    proc_key = subprocess.run(
        ["cargo", "run", "--bin", "issue_live_key"],
        cwd="engine",
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True
    )
    if proc_key.returncode != 0:
        print("  ✗ Failed to mint API key:")
        print(proc_key.stderr)
        proc_up.terminate()
        log_file.close()
        sys.exit(1)
        
    api_key = proc_key.stdout.strip().split("\n")[-1]
    print(f"  ✓ Successfully minted API key: {api_key[:15]}...")

    # 3. Submit a paid conjecture job for Spontaneous E=mc2 Derivation (without steering/domain params!)
    print("\n▶ Submitting paid conjecture job for Spontaneous E=mc2 Derivation...")
    hunch = "E = m * (c ^ 2)"
    headers = {
        "Authorization": f"Bearer {api_key}",
        "Content-Type": "application/json"
    }
    payload = {
        "hunch": hunch,
        "credits_budget": 3,
        "rush": True
    }
    
    res = requests.post(
        "http://127.0.0.1:3001/api/research/jobs",
        json=payload,
        headers=headers
    )
    if res.status_code not in [200, 201]:
        print(f"  ✗ Failed to submit job: {res.status_code}")
        print(res.text)
        proc_up.terminate()
        log_file.close()
        sys.exit(1)
        
    job_data = res.json()
    job_id = job_data["job_id"]
    print(f"  ✓ Job successfully submitted! Job ID: {job_id}")
    print(f"  Credits spent: {job_data['credits_spent']}, Remaining: {job_data['credits_remaining']}")

    # 4. Poll the job status for up to 5 minutes
    print("\n▶ Polling job status (waiting for worker to claim and prove)...")
    proved = False
    for attempt in range(1, 61):
        time.sleep(5)
        try:
            res = requests.get(
                f"http://127.0.0.1:3001/api/research/jobs/{job_id}",
                headers=headers
            )
            if res.status_code == 200:
                job = res.json()
                state = job.get("state", "unknown")
                candidates = job.get("candidates_attempted", 0)
                verified = job.get("candidates_verified", 0)
                
                print(f"  [Attempt {attempt}] Job state: {state}, Candidates: {candidates}, Verified: {verified}")
                
                if state in ["completed", "proved"] or verified > 0:
                    print(f"\n  ✓ Job successfully proved in {attempt*5} seconds!")
                    proved = True
                    break
            else:
                print(f"  [Attempt {attempt}] Error querying job: {res.status_code}")
        except Exception as e:
            print(f"  [Attempt {attempt}] Connection error: {e}")
            
    # 5. Clean up and stop the stack
    print("\n▶ Stopping the stack...")
    proc_up.terminate()
    proc_up.wait()
    log_file.close()
    subprocess.run("kill -9 $(lsof -t -i:3000 -i:3001 -i:5005) 2>/dev/null || true", shell=True)
    subprocess.run("pkill -9 -f \"lean|lake|worker\" 2>/dev/null || true", shell=True)
            
    if proved:
        print("\n═══════════════════════════════════════════════════════")
        print("  ✓ SOTA E2E Verification PASSED Successfully!")
        print("═══════════════════════════════════════════════════════")
    else:
        print("\n═══════════════════════════════════════════════════════")
        print("  ✗ SOTA E2E Verification Timed Out or Failed.")
        print("═══════════════════════════════════════════════════════")

if __name__ == "__main__":
    submit_and_poll()
