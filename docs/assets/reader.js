/* The examples illustrate the mathematics; no simulations are used as proofs. */
(() => {
  function fraction(numerator, denominator = 1) {
    const sign = numerator < 0 ? "−" : "";
    let a = Math.abs(numerator), b = denominator;
    while (b) [a, b] = [b, a % b];
    const divisor = a || 1;
    const n = Math.abs(numerator) / divisor, d = denominator / divisor;
    return sign + n + (d === 1 ? "" : "/" + d);
  }

  const choice = document.querySelector("#weight-choice");
  const rearrange = document.querySelector("#shuffle-values");
  if (choice && rearrange) {
    let values = [1, 1, 1, -1];
    // Each numerator is over 4, so all example arithmetic stays exact.
    const presets = { average: [2, 2, 0, 0], contrast: [4, -4, 0, 0], all: [1, 1, 1, 1] };
    function updateWeights() {
      const weights = presets[choice.value];
      const weightSum = weights.reduce((total, value) => total + value, 0);
      const centered = weights.map(value => 4 * value - weightSum);
      const tNumerator = centered.reduce((total, value, i) => total + value * values[i], 0);
      const rows = [
        ["#measurement-row", values.map(value => value === 1 ? "+1" : "−1")],
        ["#padded-row", weights.map(value => fraction(value, 4))],
        ["#centered-row", centered.map(value => fraction(value, 16))]
      ];
      rows.forEach(([selector, texts]) => {
        document.querySelectorAll(`${selector} td`).forEach((cell, i) => { cell.textContent = texts[i]; });
      });
      const t = fraction(tNumerator, 16);
      const explanations = {
        average: `The first two average to ${fraction(values[0] + values[1], 2)}, so T = ${fraction(values[0] + values[1], 2)} − 1/2 = ${t}.`,
        contrast: `The common average cancels: T = ${values[0]} − (${values[1]}) = ${t}.`,
        all: "The two averages coincide: T = 0 for every arrangement. All centered weights are zero."
      };
      document.querySelector("#weight-result").textContent = explanations[choice.value];
    }
    choice.addEventListener("change", updateWeights);
    rearrange.addEventListener("click", () => {
      // Cycle through the four distinct arrangements of this fixed bag.
      // This is a walkthrough, rather than a random-sampling experiment.
      values = [values[3], ...values.slice(0, 3)];
      updateWeights();
    });
    choice.disabled = rearrange.disabled = false;
    updateWeights();
  }

  const next = document.querySelector("#next-subset");
  const reset = document.querySelector("#reset-subset");
  if (next && reset) {
    const selections = [];
    for (let a = 0; a < 5; a++)
      for (let b = a + 1; b < 6; b++)
        for (let c = b + 1; c < 7; c++)
          for (let d = c + 1; d < 8; d++) selections.push([a, b, c, d]);
    const initial = selections.findIndex(s => s.join(",") === "0,2,4,7");
    let index = initial;
    function updateSubset() {
      const selected = selections[index];
      const h = selected.filter(i => i < 3).length;
      const lower = 4 - h;
      const sum = fraction(8 * h - 12, 8);
      const group = document.querySelector("#selection-markers");
      group.replaceChildren();
      function mark(cx, radius, fill, stroke) {
        const circle = document.createElementNS("http://www.w3.org/2000/svg", "circle");
        circle.setAttribute("cx", cx);
        circle.setAttribute("cy", 246);
        circle.setAttribute("r", radius);
        circle.setAttribute("fill", fill);
        if (stroke) { circle.setAttribute("stroke", stroke); circle.setAttribute("stroke-width", 2); }
        group.appendChild(circle);
      }
      for (let i = 0; i < 8; i++) {
        const cx = 110 + 60 * i;
        if (selected.includes(i)) {
          mark(cx, 9, "white", "var(--teal)");
          if (i < 3) mark(cx, 4, "var(--teal)");
        } else mark(cx, 3, "var(--line)");
      }
      document.querySelector("#subset-h").textContent = `H = ${h}`;
      const positions = selected.map(i => i + 1).join(", ");
      document.querySelector("#subset-result").textContent = `Positions ${positions}: ${h} upper value${h === 1 ? "" : "s"} and ${lower} lower value${lower === 1 ? "" : "s"}. The sum is ${h} × (5/8) + ${lower} × (−3/8) = ${sum}.`;
      document.querySelector("#levels-description").textContent = `The first three coordinates have value five eighths and the remaining five have value minus three eighths. The selected positions are ${positions}. There are ${h} selected upper values; the subset sum is ${sum}.`;
    }
    // A fixed traversal explores different positions and counts.
    // Adding 17 modulo 70 visits every four-element subset once per cycle.
    next.addEventListener("click", () => { index = (index + 17) % selections.length; updateSubset(); });
    reset.addEventListener("click", () => { index = initial; updateSubset(); });
    next.disabled = reset.disabled = false;
    updateSubset();
  }
})();
