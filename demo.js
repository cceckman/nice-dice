import init, { distribution_table } from "./pkg/nice_dice.js";

async function run() {
    await init(); // wasm_bindgen-provided

    let formula = document.getElementById("formula");
    let input = document.getElementById("input");
    let parsed = document.getElementById("parsed");

    input.addEventListener("submit", (e) => {
        e.preventDefault()

        distribution_table(formula.value).then((result) => {
            ;
            parsed.innerHTML = result;
        });
    })

    for (const example of document.querySelectorAll(".example")) {
        const text = example.innerText;
        const link = document.createElement("button");
        link.innerText = text;
        link.addEventListener("click", (e) => {
            e.preventDefault()
            formula.value = text;
            input.requestSubmit()
        })
        example.replaceChildren(link)
    }
}

run();
