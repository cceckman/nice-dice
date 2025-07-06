import init, { canonicalize, distribution_table } from "./pkg/dicer.js";

async function run() {
    await init(); // wasm_bindgen-provided

    let formula = document.getElementById("formula");
    let input = document.getElementById("input");
    let parsed = document.getElementById("parsed");

    input.addEventListener("submit", (e) => {
        e.preventDefault()

        // TODO: Can we have this run async?
        let result = distribution_table(formula.value);
        parsed.innerHTML = result;
    })
}

run();
