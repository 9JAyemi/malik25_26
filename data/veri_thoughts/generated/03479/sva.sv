module mux2to1_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic sel,
    input logic y
);

    // Output must match the RTL mux equation.
    check_mux_equation: assert property (
        @(posedge clk) y === ((sel == 1'b0) ? a : b)
    );

    // When select is 0, output must equal input a.
    check_select_a_path: assert property (
        @(posedge clk) (sel === 1'b0) |-> (y === a)
    );

    // When select is 1, output must equal input b.
    check_select_b_path: assert property (
        @(posedge clk) (sel === 1'b1) |-> (y === b)
    );

    // If both data inputs are 0, output must be 0.
    check_both_inputs_zero: assert property (
        @(posedge clk) ((a === 1'b0) && (b === 1'b0)) |-> (y === 1'b0)
    );

    // If both data inputs are 1, output must be 1.
    check_both_inputs_one: assert property (
        @(posedge clk) ((a === 1'b1) && (b === 1'b1)) |-> (y === 1'b1)
    );

endmodule