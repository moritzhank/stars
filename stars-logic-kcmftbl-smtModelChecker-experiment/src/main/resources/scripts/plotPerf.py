import sys
import numpy as np
import matplotlib.pyplot as plt

def main():
    title = sys.argv[1]
    xlabel = sys.argv[2]
    ylabel = sys.argv[3]
    saveFile = sys.argv[4]

    # data1
    fileName1 = sys.argv[5]
    legend1 = sys.argv[6]
    scaling1 = sys.argv[7]
    data1 = np.loadtxt(open(fileName1, "rb"), delimiter=",", skiprows=1)
    data1_x = np.concatenate(data1[:, :1], axis=0)
    repetitions = data1[:, 1:].shape[1]
    data1_y = (data1[:, 1:] @ np.ones((repetitions, 1))) / repetitions * float(scaling1)

    # data2
    if len(sys.argv) > 8:
        fileName2 = sys.argv[8]
        legend2 = sys.argv[9]
        scaling2 = sys.argv[10]
        data2 = np.loadtxt(open(fileName2, "rb"), delimiter=",", skiprows=1)
        data2_x = np.concatenate(data2[:, :1], axis=0)
        repetitions = data2[:, 1:].shape[1]
        data2_y = (data2[:, 1:] @ np.ones((repetitions, 1))) / repetitions * float(scaling2)

    # Plot
    plt.figure(figsize=(8, 6))
    plt.title(title)
    plt.xlabel(xlabel)
    plt.ylabel(ylabel)
    plt.plot(data1_x, data1_y, marker="o",label=legend1)
    if len(sys.argv) > 8:
        plt.plot(data2_x, data2_y, marker="o",label=legend2)
    plt.legend()
    if saveFile == "<plot>":
        plt.show()
    else:
        plt.savefig(saveFile, dpi=300)
    
if __name__ == "__main__":
    main()
