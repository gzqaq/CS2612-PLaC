import subprocess
from absl import app, flags

FLAGS = flags.FLAGS
flags.DEFINE_bool("print", False, "Print TAC output")


def generate_TAC(path: str) -> str:
  """ Generate TAC of given source file """
  cmd = f"./while_db_naive_compiler/main < {path}"
  return subprocess.check_output(cmd, shell=True, text=True)


def get_answer(src_num: int) -> str:
  if src_num < 0 or src_num > 6:
    print(f"No src output {src_num}, try some value between 0 and 6.")
    exit(1)

  path = f"samples/sample_src{src_num:02d}_output.txt"
  with open(path, "r") as f:
    ans = f.read()

  return ans


def show_difference(res: str, ans: str) -> None:
  res_lines = res.split("\n")
  ans_lines = ans.split("\n")

  for i in range(len(res_lines)):
    if res_lines[i] != ans_lines[i]:
      print(f"Line {i+1}\n  [x]: {res_lines[i]}")
      print(f"  [√]: {ans_lines[i]}")


def main(argv):
  if len(argv) != 2:
    print(
        f"Require one argument specifying src number or file name, but found {len(argv) - 1}."
    )
    exit(1)

  src_info = argv[-1]
  if src_info[0] == "s":
    src_path = src_info
    print(generate_TAC(src_path))
  else:
    src_num = int(src_info)
    src_path = f"samples/sample_src{src_num:02d}.jtl"

    res = generate_TAC(src_path)
    ans = get_answer(src_num)
    correct = res == ans

    if correct:
      print("Correct!")
    else:
      print("Not the same output.")
      show_difference(res, ans)

    if FLAGS.print:
      print(res)


if __name__ == "__main__":
  app.run(main)
