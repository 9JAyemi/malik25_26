module binary_add_sub_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic mode,
    input logic [3:0] Y
);

// In add mode, Y equals A + B.
    check_add_mode_result: assert property (
        @(posedge clk) (mode == 1'b0) |-> (Y == (A + B))
    );

// In subtract mode, Y equals A + (~B + 1).
    check_sub_mode_result: assert property (
        @(posedge clk) (mode == 1'b1) |-> (Y == (A + ((~B) + 4'b0001)))
    );

// In subtract mode, Y equals A - B.
    check_sub_mode_equivalence: assert property (
        @(posedge clk) (mode == 1'b1) |-> (Y == (A - B))
    );

// In add mode, 0 on B passes A through.
    check_add_zero_b_passthrough: assert property (
        @(posedge clk) (mode == 1'b0 && B == 4'h0) |-> (Y == A)
    );

// In subtract mode, 0 on B passes A through.
    check_sub_zero_b_passthrough: assert property (
        @(posedge clk) (mode == 1'b1 && B == 4'h0) |-> (Y == A)
    );

// In add mode, 0 on A passes B through.
    check_add_zero_a_passthrough: assert property (
        @(posedge clk) (mode == 1'b0 && A == 4'h0) |-> (Y == B)
    );

// In subtract mode, 0 on A equals ~B + 1.
    check_sub_zero_a_result: assert property (
        @(posedge clk) (mode == 1'b1 && A == 4'h0) |-> (Y == ((~B) + 4'b0001))
    );

// In add mode, 4'hF on B equals A + 4'hF.
    check_add_all_ones_b_result: assert property (
        @(posedge clk) (mode == 1'b0 && B == 4'hF) |-> (Y == (A + 4'hF))
    );

// In subtract mode, 4'hF on B equals A - 1.
    check_sub_all_ones_b_result: assert property (
        @(posedge clk) (mode == 1'b1 && B == 4'hF) |-> (Y == (A - 4'h1))
    );

endmodule
