module mux2to1_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic sel,
    input logic out
);

    // sel equal to 0 routes a to out.
    check_sel_zero_routes_a: assert property (
        @(posedge clk) (sel === 1'b0) |-> (out === a)
    );

    // Any sel value other than 0 routes b to out.
    check_sel_not_zero_routes_b: assert property (
        @(posedge clk) (sel !== 1'b0) |-> (out === b)
    );

    // Equal data inputs must appear unchanged at out.
    check_equal_inputs_preserved: assert property (
        @(posedge clk) (a === b) |-> (out === a)
    );

    // With different inputs, out matching a means sel is 0.
    check_output_a_requires_sel_zero: assert property (
        @(posedge clk) ((a !== b) && (out === a)) |-> (sel === 1'b0)
    );

    // With different inputs, out matching b means sel is not 0.
    check_output_b_requires_sel_not_zero: assert property (
        @(posedge clk) ((a !== b) && (out === b)) |-> (sel !== 1'b0)
    );

endmodule