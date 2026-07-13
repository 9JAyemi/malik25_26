module mux_2to1_comb_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic sel_b1,
    input logic sel_b2,
    input logic out_always
);

    // Output must implement the mux function defined by the select inputs.
    check_mux_function_exact: assert property (
        @(posedge clk) out_always === (((sel_b1 === 1'b1) && (sel_b2 === 1'b1)) ? b : a)
    );

    // When both select inputs are high, the output must follow b.
    check_select_b_when_both_high: assert property (
        @(posedge clk) ((sel_b1 === 1'b1) && (sel_b2 === 1'b1)) |-> (out_always === b)
    );

    // In every other select case, the output must follow a.
    check_select_a_otherwise: assert property (
        @(posedge clk) ((sel_b1 !== 1'b1) || (sel_b2 !== 1'b1)) |-> (out_always === a)
    );

endmodule