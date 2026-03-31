module twos_complement_sva (
    input logic       clk,
    input logic [3:0] Y,
    input logic [3:0] A,
    input logic       invert
);

    // Y always matches the RTL's selected combinational expression.
    check_output_matches_rtl: assert property (
        @(posedge clk) Y == (invert ? ~((~A) + 4'h1) : ((~A) + 4'h1))
    );

    // When invert is low, Y is ~A plus one.
    check_noninvert_branch: assert property (
        @(posedge clk) !invert |-> (Y == ((~A) + 4'h1))
    );

    // When invert is high, Y is the complement of ~A plus one.
    check_invert_branch: assert property (
        @(posedge clk) invert |-> (Y == ~((~A) + 4'h1))
    );

    // If A and invert stay the same, Y also stays the same.
    check_stable_inputs_hold_output: assert property (
        @(posedge clk) $stable(A) && $stable(invert) |-> $stable(Y)
    );

    // A value of zero produces zero when invert is low.
    check_zero_noninvert: assert property (
        @(posedge clk) !invert && (A == 4'h0) |-> (Y == 4'h0)
    );

    // A value of zero produces all ones when invert is high.
    check_zero_invert: assert property (
        @(posedge clk) invert && (A == 4'h0) |-> (Y == 4'hF)
    );

    // A value of all ones produces one when invert is low.
    check_allones_noninvert: assert property (
        @(posedge clk) !invert && (A == 4'hF) |-> (Y == 4'h1)
    );

    // A value of all ones produces fourteen when invert is high.
    check_allones_invert: assert property (
        @(posedge clk) invert && (A == 4'hF) |-> (Y == 4'hE)
    );

endmodule