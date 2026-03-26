module dut_mux2_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic sel,
    input logic y
);

    // When select is high, the output must follow input b.
    check_sel_high_selects_b: assert property (
        @(posedge clk) (sel === 1'b1) |-> (y === b)
    );

    // When select is low, the output must follow input a.
    check_sel_low_selects_a: assert property (
        @(posedge clk) (sel === 1'b0) |-> (y === a)
    );

    // If both data inputs are equal, the output must match that value.
    check_equal_inputs_pass_through: assert property (
        @(posedge clk) (a === b) |-> (y === a)
    );

    // The output must always match one of the two data inputs.
    check_output_is_from_inputs: assert property (
        @(posedge clk) ((y === a) || (y === b))
    );

endmodule