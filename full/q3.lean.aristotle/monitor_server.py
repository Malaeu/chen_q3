#!/usr/bin/env python3
"""
Simple monitoring server for Aristotle projects.
Proxies API requests to avoid CORS issues.

Usage:
    python monitor_server.py
    # Then open http://localhost:8080
"""

import asyncio
import json
import os
from http.server import HTTPServer, SimpleHTTPRequestHandler
from urllib.parse import urlparse, parse_qs
import http.client
import ssl

API_KEY = os.environ.get("ARISTOTLE_API_KEY", "")
BASE_URL = "aristotle.harmonic.fun"
API_PATH = "/api/v1"

# Q3 Project IDs
Q3_PROJECTS = [
    ("01_T0_normalization", "98c4ed76-fce8-4e58-b3ca-46f8c6d3f6e6"),
    ("02_A1prime_local_density", "098c51d6-908e-4a65-a15a-65e9060e6358"),
    ("03_A2_lipschitz", "8337e17d-d2ca-4231-adb9-929e45e3fc8f"),
    ("04_A3_toeplitz_main", "f62e1767-5adb-4d52-99cc-58831c8201c6"),
    ("05_RKHS_prime_cap", "34be4dc5-7272-42a8-9be8-59f4be0d90f8"),
    ("06_T5_transfer", "f3991944-86d5-4667-93d4-d7d19dc15dab"),
    ("07_Main_closure", "6e8bdd2f-2503-471e-a132-b81a36a31b1f"),
]


class MonitorHandler(SimpleHTTPRequestHandler):
    def do_GET(self):
        parsed = urlparse(self.path)

        if parsed.path == "/api/status":
            self.handle_status()
        elif parsed.path.startswith("/api/download/"):
            project_id = parsed.path.split("/")[-1]
            self.handle_download(project_id)
        elif parsed.path.startswith("/api/input/"):
            project_name = parsed.path.split("/")[-1]
            self.handle_input(project_name)
        else:
            # Serve static files
            super().do_GET()

    def handle_input(self, project_name):
        """Serve input file content"""
        # Get script directory (works even when __file__ is relative)
        script_dir = os.path.dirname(os.path.abspath(__file__))
        input_dir = os.path.join(script_dir, "input")

        print(f"[DEBUG] Looking for input: {project_name}")
        print(f"[DEBUG] Script dir: {script_dir}")
        print(f"[DEBUG] Input dir: {input_dir}")

        # Try different filename patterns
        patterns = [
            f"{project_name}.md",
        ]

        for pattern in patterns:
            filepath = os.path.join(input_dir, pattern)
            print(f"[DEBUG] Checking: {filepath} exists={os.path.exists(filepath)}")
            if os.path.exists(filepath):
                try:
                    with open(filepath, 'r', encoding='utf-8') as f:
                        content = f.read()
                    self.send_response(200)
                    self.send_header("Content-Type", "text/plain; charset=utf-8")
                    self.send_header("Access-Control-Allow-Origin", "*")
                    self.end_headers()
                    self.wfile.write(content.encode('utf-8'))
                    return
                except Exception as e:
                    self.send_json({"error": str(e)}, status=500)
                    return

        # List available files for debugging
        available = []
        if os.path.exists(input_dir):
            available = os.listdir(input_dir)

        self.send_response(404)
        self.send_header("Content-Type", "text/plain")
        self.send_header("Access-Control-Allow-Origin", "*")
        self.end_headers()
        msg = f"Input file not found: {project_name}.md\nDirectory: {input_dir}\nAvailable: {available}"
        self.wfile.write(msg.encode())

    def handle_status(self):
        """Get status of all Q3 projects"""
        results = []
        import datetime
        local_time = datetime.datetime.now().isoformat()

        for name, pid in Q3_PROJECTS:
            try:
                data = self.fetch_project(pid)
                results.append({
                    "name": name,
                    "id": pid,
                    "status": data.get("status", "UNKNOWN"),
                    "percent_complete": data.get("percent_complete", 0),
                    "created_at": data.get("created_at"),
                    "last_updated_at": data.get("last_updated_at"),
                    "local_check": local_time,
                })
            except Exception as e:
                results.append({
                    "name": name,
                    "id": pid,
                    "status": "ERROR",
                    "error": str(e),
                    "local_check": local_time,
                })

        self.send_json({"projects": results, "checked_at": local_time})

    def handle_download(self, project_id):
        """Download solution for a project"""
        try:
            conn = http.client.HTTPSConnection(BASE_URL)
            conn.request(
                "GET",
                f"{API_PATH}/project/{project_id}/result",
                headers={"X-API-Key": API_KEY}
            )
            response = conn.getresponse()

            if response.status == 200:
                content = response.read()
                self.send_response(200)
                self.send_header("Content-Type", "application/octet-stream")
                self.send_header("Content-Disposition", f"attachment; filename={project_id}.lean")
                self.end_headers()
                self.wfile.write(content)
            else:
                self.send_json({"error": f"HTTP {response.status}"}, status=response.status)
        except Exception as e:
            self.send_json({"error": str(e)}, status=500)

    def fetch_project(self, project_id):
        """Fetch project status from Aristotle API"""
        conn = http.client.HTTPSConnection(BASE_URL)
        conn.request(
            "GET",
            f"{API_PATH}/project/{project_id}",
            headers={"X-API-Key": API_KEY}
        )
        response = conn.getresponse()
        if response.status != 200:
            raise Exception(f"HTTP {response.status}")
        return json.loads(response.read().decode())

    def send_json(self, data, status=200):
        self.send_response(status)
        self.send_header("Content-Type", "application/json")
        self.send_header("Access-Control-Allow-Origin", "*")
        self.end_headers()
        self.wfile.write(json.dumps(data).encode())


def main():
    port = 8080

    if not API_KEY:
        print("⚠️  ARISTOTLE_API_KEY not set!")
        print("Run: export ARISTOTLE_API_KEY='your_key_here'")
        return

    print(f"""
╔══════════════════════════════════════════════════╗
║       🔬 Aristotle Monitor Server                ║
╠══════════════════════════════════════════════════╣
║  Open: http://localhost:{port}/monitor_local.html  ║
║  API:  http://localhost:{port}/api/status          ║
╚══════════════════════════════════════════════════╝
    """)

    server = HTTPServer(("", port), MonitorHandler)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\n👋 Server stopped")


if __name__ == "__main__":
    main()
