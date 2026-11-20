"""Generate the narration using an installed Kokoro v1.0 model and voices."""
import argparse
import json
import re
from pathlib import Path
import numpy as np
import soundfile as sf
from kokoro_onnx import Kokoro

parser = argparse.ArgumentParser()
parser.add_argument("model_dir", type=Path)
params = parser.parse_args()
engine = Kokoro(str(params.model_dir / "kokoro-v1.0.onnx"), str(params.model_dir / "voices-v1.0.bin"))
spoken_numbers = {
    "22": "twenty-two",
    "64": "sixty-four",
    "165": "one hundred sixty-five",
    "189": "one hundred eighty-nine",
    "220": "two hundred twenty",
    "283": "two hundred eighty-three",
    "350": "three hundred fifty",
    "364": "three hundred sixty-four",
    "408": "four hundred eight",
    "570": "five hundred seventy",
    "780": "seven hundred eighty",
}
track, cues = [], []
rate = 24000
samples = 0
for scene, lines in enumerate(json.loads(Path("story.json").read_text())):
    for line in lines:
        lead = np.zeros(round(rate * 0.22), dtype="float32")
        tail = np.zeros(round(rate * 0.30), dtype="float32")
        spoken = re.sub(r"\b\d+\b", lambda match: spoken_numbers[match[0]], line)
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
