import subprocess
import time
import requests

def test_server():
    print("Starting FastAPI server on port 5005...")
    proc = subprocess.Popen(
        ["python3", "rl_agent/server.py"],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True
    )
    
    # Wait for the server to boot
    time.sleep(5)
    
    try:
        print("Testing /status endpoint...")
        res = requests.get("http://127.0.0.1:5005/status")
        print("Status Response:", res.json())
        
        print("Testing /predict endpoint...")
        obs = [0.5] * 48
        res = requests.post(
            "http://127.0.0.1:5005/predict",
            json={"observation": obs}
        )
        print("Predict Response:", res.json())
        
    except Exception as e:
        print("Error during test:", e)
        # Print server logs
        stdout, stderr = proc.communicate(timeout=1)
        print("Server stdout:", stdout)
        print("Server stderr:", stderr)
    finally:
        print("Stopping FastAPI server...")
        proc.terminate()
        proc.wait()

if __name__ == "__main__":
    test_server()
