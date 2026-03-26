module addsub_4bit_sva (
    input logic        clk,
    input logic [3:0]  A,
    input logic [3:0]  B,
    input logic        S,
    input logic [3:0]  F
);

    // F matches the selected arithmetic operation every sampled cycle.
    check_selected_operation: assert property (
        @(posedge clk) F == (S ? (A - B) : (A + B))
    );

    // In add mode, F is the 4-bit sum of A and B.
    check_add_mode_result: assert property (
        @(posedge clk) (S == 1'b0) |-> (F == (A + B))
    );

    // In subtract mode, F is the 4-bit difference of A and B.
    check_sub_mode_result: assert property (
        @(posedge clk) (S == 1'b1) |-> (F == (A - B))
    );

    // Adding zero on B passes A through to F.
    check_add_zero_on_b: assert property (
        @(posedge clk) ((S == 1'b0) && (B == 4'h0)) |-> (F == A)
    );

    // Adding zero on A passes B through to F.
    check_add_zero_on_a: assert property (
        @(posedge clk) ((S == 1'b0) && (A == 4'h0)) |-> (F == B)
    );

    // Subtracting zero on B passes A through to F.
    check_sub_zero_on_b: assert property (
        @(posedge clk) ((S == 1'b1) && (B == 4'h0)) |-> (F == A)
    );

    // Subtracting equal operands produces zero.
    check_sub_equal_operands_zero: assert property (
        @(posedge clk) ((S == 1'b1) && (A == B)) |-> (F == 4'h0)
    );

endmodule