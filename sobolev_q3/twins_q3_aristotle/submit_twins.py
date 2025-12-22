#!/usr/bin/env python3
"""
Submit Twin Primes Q3 lemmas to Aristotle.

Usage:
    python submit_twins.py                    # Submit all input files
    python submit_twins.py Q3_twins_mod6.md   # Submit specific file
    python submit_twins.py --status           # Check status of all projects
"""

import asyncio
import sys
import os
from pathlib import Path

# Ensure API key is set
if "ARISTOTLE_API_KEY" not in os.environ:
    print("❌ Set ARISTOTLE_API_KEY first:")
    print('   export ARISTOTLE_API_KEY="your_key"')
    sys.exit(1)

from aristotlelib import Project, set_api_key, ProjectInputType

set_api_key(os.environ["ARISTOTLE_API_KEY"])

INPUT_DIR = Path(__file__).parent / "aristotle_input"
OUTPUT_DIR = Path(__file__).parent / "aristotle_output"
STATUS_FILE = Path(__file__).parent / "project_ids.txt"


async def submit_file(filepath: Path) -> str | None:
    """Submit a single file to Aristotle."""
    print(f"📤 Submitting: {filepath.name}")

    try:
        # wait_for_completion=False returns project_id string directly
        project_id = await Project.prove_from_file(
            input_file_path=str(filepath),
            auto_add_imports=False,
            validate_lean_project=False,
            project_input_type=ProjectInputType.INFORMAL,
            wait_for_completion=False,  # Don't wait, return project ID immediately
        )
        print(f"   ✅ Submitted! Project ID: {project_id}")
        # Get project object for status
        project = await Project.from_id(project_id)
        print(f"   📊 Status: {project.status}")
        return project_id
    except Exception as e:
        print(f"   ❌ Error: {e}")
        return None


async def check_status():
    """Check status of all projects."""
    print("📊 Checking project statuses...")
    print("=" * 60)

    if not STATUS_FILE.exists():
        print("❌ No project_ids.txt found. Submit files first.")
        return

    with open(STATUS_FILE) as f:
        lines = f.readlines()

    for line in lines:
        if ":" not in line:
            continue
        name, pid = line.strip().split(":", 1)
        pid = pid.strip()

        try:
            p = await Project.from_id(pid)
            status_emoji = {
                "COMPLETE": "✅",
                "IN_PROGRESS": "🔄",
                "QUEUED": "⏳",
                "FAILED": "❌",
            }.get(str(p.status), "❓")

            print(f"{status_emoji} {name}: {p.status} ({p.percent_complete}%)")

            # Download if complete
            if str(p.status) == "COMPLETE":
                output_file = OUTPUT_DIR / f"{name.replace('.md', '')}_aristotle.lean"
                if not output_file.exists():
                    await p.get_solution(str(output_file))
                    print(f"   📥 Downloaded: {output_file.name}")
        except Exception as e:
            print(f"❓ {name}: Error - {e}")


async def submit_all():
    """Submit all input files."""
    print("🚀 Submitting Twin Primes Q3 lemmas to Aristotle")
    print("=" * 60)

    input_files = sorted(INPUT_DIR.glob("*.md"))

    if not input_files:
        print(f"❌ No .md files found in {INPUT_DIR}")
        return

    print(f"📁 Found {len(input_files)} input files\n")

    project_ids = []
    for f in input_files:
        pid = await submit_file(f)
        if pid:
            project_ids.append((f.name, pid))
        print()

    # Save project IDs
    with open(STATUS_FILE, "w") as f:
        for name, pid in project_ids:
            f.write(f"{name}: {pid}\n")

    print("=" * 60)
    print("📋 Summary:")
    for name, pid in project_ids:
        print(f"   {name}: {pid}")

    print(f"\n✅ Submitted {len(project_ids)} projects")
    print(f"📝 Project IDs saved to: {STATUS_FILE}")
    print("\n💡 Check status with:")
    print("   python submit_twins.py --status")


async def submit_one(filename: str):
    """Submit a specific file."""
    filepath = INPUT_DIR / filename
    if not filepath.exists():
        print(f"❌ File not found: {filepath}")
        return

    pid = await submit_file(filepath)
    if pid:
        # Append to status file
        with open(STATUS_FILE, "a") as f:
            f.write(f"{filename}: {pid}\n")
        print(f"📝 Added to {STATUS_FILE}")


async def main():
    if len(sys.argv) < 2:
        await submit_all()
    elif sys.argv[1] == "--status":
        await check_status()
    else:
        await submit_one(sys.argv[1])


if __name__ == "__main__":
    asyncio.run(main())
