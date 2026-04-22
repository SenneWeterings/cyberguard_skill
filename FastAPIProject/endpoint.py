from fastapi import FastAPI
import subprocess

app = FastAPI()

@app.post("/run")
def run_script(password: str, mode: int):
    try:
        process = subprocess.Popen(
            ["dotnet", "run", "-c", "Release"],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True
        )

        # input simuleren (zoals console input)
        input_data = f"{mode}\n{password}\n"
        output, error = process.communicate(input=input_data)

        return {
            "output": output,
            "error": error
        }

    except Exception as e:
        return {"error": str(e)}