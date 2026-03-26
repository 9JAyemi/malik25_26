module arithmetic_module_sva (
    input logic clk,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic CTRL,
    input logic [7:0] RESULT
);

    // RESULT is the 8-bit sum when CTRL is exactly 0.
    check_add_mode: assert property (
        @(posedge clk) (CTRL === 1'b0) |-> (RESULT == (A + B))
    );

    // RESULT is the 8-bit difference when CTRL is not exactly 0.
    check_sub_mode: assert property (
        @(posedge clk) (CTRL !== 1'b0) |-> (RESULT == (A - B))
    );

    // With unchanged inputs, RESULT remains unchanged.
    check_pure_combinational_stability: assert property (
        @(posedge clk) $stable({A, B, CTRL}) |-> $stable(RESULT)
    );

endmodule