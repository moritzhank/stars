import os
import platform
import subprocess

# Generated with GPT-4o from OpenAI and modified
def download_cvc5():
    architecture = platform.machine()
    arch_map = {
        "x86_64": "Linux-x86_64",
        "aarch64": "Linux-arm64",
        "arm64": "Linux-arm64",
        "amd64": "Linux-x86_64"
    }
    if architecture not in arch_map:
        raise Exception(f"Architecture {architecture} is not supported.")
    cvc5_version = "1.2.0"
    cvc5_base_url = f"https://github.com/cvc5/cvc5/releases/download/cvc5-{cvc5_version}/"
    cvc5_filename = f"cvc5-{arch_map[architecture]}-static.zip"
    cvc5_url = cvc5_base_url + cvc5_filename
    subprocess.run(["wget", cvc5_url], check=True)
    if os.path.exists(cvc5_filename):
        subprocess.run(["unzip", cvc5_filename], check=True)
        subprocess.run(["rm", cvc5_filename], check=True)
        cvc5_filename = cvc5_filename[:-4]
        subprocess.run(["mv", f"{cvc5_filename}/bin/cvc5", "cvc5"], check=True)
        subprocess.run(["rm", "-r", cvc5_filename], check=True)
    else:
        raise Exception(f"Error: {cvc5_filename} could not be downloaded.")

if __name__ == "__main__":
    download_cvc5()