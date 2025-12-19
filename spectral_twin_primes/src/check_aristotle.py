#!/usr/bin/env python3
"""
Aristotle Project Manager.

Usage:
    python check_aristotle.py                     # List all projects
    python check_aristotle.py PROJECT_ID          # Check specific project
    python check_aristotle.py dad24643-...        # Example
"""

import asyncio
import sys
import os

# Ensure API key is set
if "ARISTOTLE_API_KEY" not in os.environ:
    print("❌ Set ARISTOTLE_API_KEY first:")
    print('   export ARISTOTLE_API_KEY="your_key"')
    sys.exit(1)

from aristotlelib import Project, set_api_key

set_api_key(os.environ["ARISTOTLE_API_KEY"])


async def list_all():
    """List all projects."""
    print("📋 All Aristotle Projects:")
    print("=" * 70)

    result = await Project.list_projects()
    projects = result[0] if isinstance(result, tuple) else result

    if not projects:
        print("  No projects found.")
        return

    for p in projects:
        status_emoji = {
            "QUEUED": "⏳",
            "IN_PROGRESS": "🔄",
            "COMPLETED": "✅",
            "FAILED": "❌"
        }.get(str(p.status).split('.')[-1], "❓")

        print(f"\n{status_emoji} {p.project_id}")
        print(f"   Status: {p.status} ({p.percent_complete}%)")
        print(f"   File: {p.file_name}")
        print(f"   Description: {p.description}")


async def check_one(project_id: str):
    """Check specific project."""
    print(f"🔍 Project: {project_id}")
    print("=" * 70)

    project = await Project.from_id(project_id)

    status_emoji = {
        "QUEUED": "⏳",
        "IN_PROGRESS": "🔄",
        "COMPLETED": "✅",
        "FAILED": "❌"
    }.get(str(project.status).split('.')[-1], "❓")

    print(f"{status_emoji} Status: {project.status}")
    print(f"📈 Progress: {project.percent_complete}%")
    print(f"📝 Description: {project.description}")

    if "COMPLETED" in str(project.status):
        print()
        print("=" * 70)
        print("✅ LEAN PROOF:")
        print("=" * 70)
        solution = await project.get_solution()
        print(solution)
        print("=" * 70)

    elif "FAILED" in str(project.status):
        print()
        print("❌ Proof failed. Aristotle could not find a valid proof.")


async def main():
    if len(sys.argv) < 2:
        await list_all()
    else:
        await check_one(sys.argv[1])


if __name__ == "__main__":
    asyncio.run(main())
