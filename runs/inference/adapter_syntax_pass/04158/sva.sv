module binary_add_sub_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       mode,
    input logic [3:0] Y
);

    // In add mode, Y must equal A plus B.
    check_add_mode_result: assert property (
        @($global_clock) (mode == 1'b0) |-> (Y == (A + B))
    );

    // In subtract mode, Y must equal A plus the two's complement of B.
    check_sub_mode_result: assert property (
        @($global_clock) (mode == 1'b1) |-> (Y == (A + ((~B) + 4'b0001)))
    );

    // In subtract mode, Y must equal A minus B.
    check_sub_mode_matches_subtraction: assert property (
        @($global_clock) (mode == 1'b1) |-> (Y == (A - B))
    );

    // With B at zero, the output must pass A through.
    check_zero_b_passthrough: assert property (
        @($global_clock) (B == 4'h0) |-> (Y == A)
    );

    // In add mode, adding zero must leave A unchanged.
    check_add_zero_b_passthrough: assert property (
        @($global_clock) ((mode == 1'b0) && (B == 4'h0)) |-> (Y == A)
    );

    // In subtract mode, subtracting zero must leave A unchanged.
    check_sub_zero_b_passthrough: assert property (
        @($global_clock) ((mode == 1'b1) && (B == 4'h0)) |-> (Y == A)
    );

    // In add mode, adding 4'hF must produce 4'hF.
    check_add_fills_ones: assert property (
        @($global_clock) ((mode == 1'b0) && (B == 4'hF)) |-> (Y == 4'hF)
    );

    // In subtract mode, subtracting 4'hF must produce 4'h0.
    check_sub_fills_zeros: assert property (
        @($global_clock) ((mode == 1'b1) && (B == 4'hF)) |-> (Y == 4'h0)
    );

endmodule