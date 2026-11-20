# How few polygons?

A 70-second narrated companion to *Minimum numbers of convex polygons on twelve through fourteen points* by Rohan Arun, Super Powers AI. The rendered figures use integer coordinates from the paper's reproduction package. The renderer independently enumerates convex subsets in all seven configurations and checks their counts before producing frames. Each gallery panel uses a uniform scale in both directions.

The 10- and 11-point polygon minima, 189 and 283, are credited to [Nikol Savova](https://github.com/NikolSavova/erdos-838-convex-subsets). The 12-, 13-, and 14-point results and classifications come from [the manuscript](https://doi.org/10.5281/zenodo.24397151). [Erdős problem 838](https://www.erdosproblems.com/838) asks about general growth.

## Reproduce

Run from the directory containing this README. For narration, install the Python packages kokoro-onnx, numpy and soundfile and obtain the Kokoro v1.0 ONNX model and voices-v1.0.bin from [the Kokoro ONNX project](https://github.com/thewh1teagle/kokoro-onnx). Run python3 narrate.py MODEL_DIRECTORY. The script uses the af_heart voice. It writes the narration and caption times under build/.

Install Pillow and FFmpeg with libx264 and AAC support, then run python3 render.py to generate erdos-838-explained.mp4. The typography uses Avenir Next and Georgia on macOS. On other platforms update the serif and sans font paths and indexes in render.py. The code and supplied coordinates are released under the accompanying MIT license. Fonts and voice-model weights are external dependencies.

## Timeline

| Time | Scene |
| --- | --- |
| 00:00 | A convex pentagon in the 14-point minimizing order type |
| 00:07 | The corner test with a triangle and an interior point |
| 00:16 | Savova's 10- and 11-point minima |
| 00:23 | The 12-point minimum and example polygons of each size |
| 00:35 | The five 13-point minimizing order types |
| 00:45 | The unique 14-point minimizing order type and its 780 polygons |
| 00:59 | How the computation and exclusion certificates prove the minima |
| 01:05 | A recap of the finite minima and the open asymptotic question |
