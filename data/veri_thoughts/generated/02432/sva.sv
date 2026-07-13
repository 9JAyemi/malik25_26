module mux_xor_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic sel_b1,
    input logic sel_b2,
    input logic out
);

    // out implements the exact combinational function of the RTL.
    check_out_function_equivalence: assert property (
        @(posedge clk) out == (sel_b1 ? b : (sel_b2 ? a : (a ^ b)))
    );

    // When sel_b1 is HIGH, out must equal b.
    check_sel_b1_routes_b: assert property (
        @(posedge clk) sel_b1 |-> (out == b)
    );

    // When sel_b1 is LOW and sel_b2 is HIGH, out must equal a.
    check_sel_b2_routes_a_when_b1_low: assert property (
        @(posedge clk) (!sel_b1 && sel_b2) |-> (out == a)
    );

    // When both selects are LOW, out must equal a XOR b.
    check_xor_path_when_no_selects: assert property (
        @(posedge clk) (!sel_b1 && !sel_b2) |-> (out == (a ^ b))
    );

    // When both selects are HIGH, sel_b1 has priority and out equals b.
    check_both_selects_prioritize_b: assert property (
        @(posedge clk) (sel_b1 && sel_b2) |-> (out == b)
    );

    // When exactly one select is HIGH, out equals the selected input.
    check_one_select_behavior: assert property (
        @(posedge clk) (sel_b1 ^ sel_b2) |-> (out == (sel_b1 ? b : a))
    );

    // With no selects and equal inputs, XOR path forces out LOW.
    check_xor_zero_when_inputs_equal: assert property (
        @(posedge clk) (!sel_b1 && !sel_b2 && (a == b)) |-> (out == 1'b0)
    );

    // With no selects and different inputs, XOR path forces out HIGH.
    check_xor_one_when_inputs_different: assert property (
        @(posedge clk) (!sel_b1 && !sel_b2 && (a != b)) |-> (out == 1'b1)
    );

endmodule