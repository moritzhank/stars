import sys
import numpy as np

def main():
    start = int(sys.argv[1])
    stop = int(sys.argv[2])
    num = int(sys.argv[3])
    result = "arrayOf("
    for x in np.linspace(start, stop, num):
        result += f"{str(int(x))}, "
    print(f"{result[:-2]})")

if __name__ == "__main__":
    main()
