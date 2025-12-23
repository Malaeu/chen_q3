#!/usr/bin/env python3
import asyncio
import sys
from datetime import datetime
from aristotlelib import Project, ProjectStatus

PROJECT_ID = "b92e3d07-7a36-4f06-881c-eaddff6c6789"
CHECK_INTERVAL = 300  # 5 minutes

def log(msg):
    print(msg, flush=True)

async def main():
    log(f"🔭 Watching V2 project: {PROJECT_ID[:8]}...")
    log(f"⏱️  Check interval: {CHECK_INTERVAL} seconds")
    log("=" * 50)
    
    check_num = 0
    while True:
        check_num += 1
        try:
            p = await Project.from_id(PROJECT_ID)
            pct = p.percent_complete or 0
            ts = datetime.now().strftime("%H:%M:%S")
            
            if p.status == ProjectStatus.COMPLETE:
                log(f"[{ts}] #{check_num} ✅ COMPLETE {pct:.0f}%")
                log("\n🎉 V2 PROJECT COMPLETE!")
                
                solution = await p.get_solution()
                output_file = f"v2_{PROJECT_ID[:8]}_aristotle.lean"
                with open(output_file, "w") as f:
                    f.write(solution)
                log(f"📥 Downloaded to: {output_file}")
                break
            else:
                log(f"[{ts}] #{check_num} ⏳ IN_PROGRESS {pct:.0f}%")
                log(f"    Next check in {CHECK_INTERVAL//60} minutes...")
                
        except Exception as e:
            log(f"Error: {e}")
        
        await asyncio.sleep(CHECK_INTERVAL)

if __name__ == "__main__":
    asyncio.run(main())
