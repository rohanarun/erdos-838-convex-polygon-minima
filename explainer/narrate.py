"""Generate the narration using an installed Kokoro v1.0 model and voices."""
import argparse
import json
from pathlib import Path
import numpy as np
import soundfile as sf
from kokoro_onnx import Kokoro

parser = argparse.ArgumentParser()
parser.add_argument("model_dir", type=Path)
params = parser.parse_args()
engine = Kokoro(str(params.model_dir / "kokoro-v1.0.onnx"), str(params.model_dir / "voices-v1.0.bin"))
track, cues = [], []
rate = 24000
samples = 0
for scene, lines in enumerate(json.loads(Path("story.json").read_text())):
    for line in lines:
        lead = np.zeros(round(rate * 0.22), dtype="float32")
        tail = np.zeros(round(rate * 0.30), dtype="float32")
        spoken = line.replace("189", "one hundred eighty-nine").replace("283", "two hundred eighty-three").replace("408","four hundred eight").replace("220","two hundred twenty").replace("165","one hundred sixty-five").replace("22","twenty-two").replace("570","five hundred seventy")
        audio, sr = engine.create(spoken, voice="af_heart", speed=1.05, lang="en-us")
        assert sr == rate and np.isfinite(audio).all()
        track.extend([lead, audio, tail])
        end = samples + len(lead) + len(audio) + len(tail)
        cues.append([scene, line, samples/rate, end/rate])
        samples = end
        print(scene, round(end/rate,2), flush=True)
Path("build").mkdir(exist_ok=True)
sf.write("build/narration.wav", np.concatenate(track), rate)
Path("build/cues.json").write_text(json.dumps(cues, indent=2))
