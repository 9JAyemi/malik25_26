module mux_2to1_sva(
    input logic clk,
    input logic sel,
    input logic in0,
    input logic in1,
    input logic out
);

    // Out must match the 2:1 mux Boolean equation.
    check_mux_equation: assert property (
        @(posedge clk) out == ((~sel & in0) | (sel & in1))
    );

    // When sel is LOW, out must follow in0.
    check_selects_in0: assert property (
        @(posedge clk) (sel == 1'b0) |-> (out == in0)
    );

    // When sel is HIGH, out must follow in1.
    check_selects_in1: assert property (
        @(posedge clk) (sel == 1'b1) |-> (out == in1)
    );

    // If both inputs are LOW, out must be LOW.
    check_both_inputs_low: assert property (
        @(posedge clk) ((in0 == 1'b0) && (in1 == 1'b0)) |-> (out == 1'b0)
    );

    // If both inputs are HIGH, out must be HIGH.
    check_both_inputs_high: assert property (
        @(posedge clk) ((in0 == 1'b1) && (in1 == 1'b1)) |-> (out == 1'b1)
    );

    // With in0 LOW and in1 HIGH, out must equal sel.
    check_output_equals_sel_for_01: assert property (
        @(posedge clk) ((in0 == 1'b0) && (in1 == 1'b1)) |-> (out == sel)
    );

    // With in0 HIGH and in1 LOW, out must equal inverse of sel.
    check_output_equals_not_sel_for_10: assert property (
        @(posedge clk) ((in0 == 1'b1) && (in1 == 1'b0)) |-> (out == ~sel)
    );

endmodule