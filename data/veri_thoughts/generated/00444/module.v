
module mux_4to1 (
    out,
    in0,
    in1,
    in2,
    in3,
    sel
);

    // Module ports
    output out;
    input  in0, in1, in2, in3;
    input  [1:0] sel;

    // Local signals
    wire sel0, sel1, sel2, sel3;

    // AND the select signals with the input signals
    and sel0 (sel0, in0, ~sel[0], ~sel[1]);
    and sel1 (sel1, in1, sel[0], ~sel[1]);
    and sel2 (sel2, in2, ~sel[0], sel[1]);
    and sel3 (sel3, in3, sel[0], sel[1]);

    // OR the ANDed signals to get the output
    or out_or (out, sel0, sel1, sel2, sel3);

endmodule