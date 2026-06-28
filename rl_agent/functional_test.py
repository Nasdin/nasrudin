import subprocess
import time
import requests
import os
import sys

def run_functional_test():
    print("═══════════════════════════════════════════════════════")
    print("  Nasrudin Functional End-to-End Test: Researcher Flow")
    print("═══════════════════════════════════════════════════════\n")

    # Fix unexpanded shell variables in DATABASE_URL from parent environment
    if "DATABASE_URL" in os.environ and "${POSTGRES_USER}" in os.environ["DATABASE_URL"]:
        os.environ["DATABASE_URL"] = "postgresql://physics:physics_dev@localhost:5432/physics_generator"

    # Disable persistent elaborator during test to allow instant worker boot
    os.environ["NASRUDIN_NO_PERSISTENT"] = "1"

    # 1. Start the entire stack using 'just up' in the background
    print("▶ Starting the entire stack using 'just up'...")
    # Kill any existing processes on ports 3000, 3001, 5005 and any orphan lean/lake compilers
    subprocess.run("kill -9 $(lsof -t -i:3000 -i:3001 -i:5005) 2>/dev/null || true", shell=True)
    subprocess.run("pkill -9 -f \"lean|lake\" 2>/dev/null || true", shell=True)
    
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
        sys.exit(1)

    # Purge older queued/running conjecture jobs from PostgreSQL to ensure immediate claim
    print("\n▶ Purging old conjecture jobs from database...")
    try:
        import psycopg2
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
        print(f"  ✗ Failed to mint API key: {proc_key.stderr}")
        proc_up.terminate()
        sys.exit(1)
        
    api_key = proc_key.stdout.strip().split("\n")[-1]
    print(f"  ✓ Successfully minted API key: {api_key[:15]}...")

    # 3. Submit a paid conjecture job for Single-Minus Gluon Scattering Amplitudes (2025 SOTA Discovery)
    print("\n▶ Submitting paid conjecture job for Single-Minus Gluon Scattering Amplitudes...")
    hunch = "A = (g ^ (n - 2)) * (f / (s_12 * s_23 * s_31))"
    headers = {
        "Authorization": f"Bearer {api_key}",
        "Content-Type": "application/json"
    }
    payload = {
        "hunch": hunch,
        "domain_hint": "quantum_mechanics",
        "credits_budget": 1,
        "rush": True,
        "steering": {
            "mutation_knobs": {
                "rate": 0.20,
                "population_size": 128,
                "suffix_bias": 0.6,
                "elitism_fraction": 0.1
            },
            "mutation_priors": {
                "append_productive_suffix": 2.0
            }
        }
    }
    
    res = requests.post(
        "http://127.0.0.1:3001/api/research/jobs",
        headers=headers,
        json=payload
    )
    if res.status_code != 201:
        print(f"  ✗ Failed to submit job: {res.text}")
        proc_up.terminate()
        sys.exit(1)
        
    job_data = res.json()
    job_id = job_data["job_id"]
    print(f"  ✓ Job successfully submitted! Job ID: {job_id}")
    print(f"  Credits spent: {job_data['credits_spent']}, Remaining: {job_data['credits_remaining']}")

    # 4. Poll the job status until it transitions to completed / proved
    print("\n▶ Polling job status (waiting for worker to claim and prove)...")
    proved = False
    for attempt in range(60):
        time.sleep(5)
        res = requests.get(
            f"http://127.0.0.1:3001/api/research/jobs/{job_id}",
            headers=headers
        )
        if res.status_code != 200:
            print(f"  ✗ Failed to fetch job details: {res.text}")
            break
            
        job = res.json()
        state = job["state"]
        print(f"  [Attempt {attempt+1}] Job state: {state}, Candidates attempted: {job['candidates_attempted']}")
        
        if state == "completed" or state == "proved" or job["candidates_verified"] > 0:
            print(f"\n  ✓ Job successfully proved in {attempt*5} seconds!")
            proved = True
            break
            
    # 5. Clean up and stop the stack
    print("\n▶ Stopping the stack...")
    proc_up.terminate()
    proc_up.wait()
    log_file.close()
    subprocess.run("kill -9 $(lsof -t -i:3000 -i:3001 -i:5005) 2>/dev/null || true", shell=True)
    subprocess.run("pkill -9 -f \"lean|lake\" 2>/dev/null || true", shell=True)
    
    if proved:
        print("\n═══════════════════════════════════════════════════════")
        print("  ✓ Functional End-to-End Test PASSED Successfully!")
        print("═══════════════════════════════════════════════════════")
    else:
        print("\n═══════════════════════════════════════════════════════")
        print("  ✗ Functional End-to-End Test FAILED or Timed Out.")
        print("═══════════════════════════════════════════════════════")
        sys.exit(1)

if __name__ == "__main__":
    run_functional_test()
