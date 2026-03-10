module addsub_sva (
    input logic CLK,        // External clock for sampling assertions
    input logic [3:0] A,
    input logic [3:0] B,
    input logic ctrl,
    input logic [3:0] Y
);
    // Notes: No reset in RTL; combinational logic; assertions are sampled on CLK.

    // When ctrl=1, Y equals A+B (4-bit modulo arithmetic).
    check_add_result: assert property (
        @(posedge CLK) ctrl |-> (Y == (A + B))
    );

    // When ctrl=0, Y equals A-B (4-bit modulo arithmetic).
    check_sub_result: assert property (
        @(posedge CLK) !ctrl |-> (Y == (A - B))
    );

    // If inputs are stable across cycles, output remains stable.
    check_stable_when_inputs_unchanged: assert property (
        @(posedge CLK) $stable({A,B,ctrl}) |-> $stable(Y)
    );

    // If B is zero, output equals A regardless of ctrl.
    check_b_zero_returns_a: assert property (
        @(posedge CLK) (B == 4'd0) |-> (Y == A)
    );

    // If ctrl=1 and A is zero, output equals B.
    check_add_a_zero_returns_b: assert property (
        @(posedge CLK) (ctrl && (A == 4'd0)) |-> (Y == B)
    );

    // If ctrl=0 and A==B, output is zero.
    check_sub_self_zero: assert property (
        @(posedge CLK) (!ctrl && (A == B)) |-> (Y == 4'd0)
    );

    // Wrap-around example: 0xF + 1 -> 0 when adding.
    check_add_wrap_ff_plus_1: assert property (
        @(posedge CLK) (ctrl && (A == 4'hF) && (B == 4'd1)) |-> (Y == 4'h0)
    );

    // Wrap-around example: 0 - 1 -> 0xF when subtracting.
    check_sub_wrap_0_minus_1: assert property (
        @(posedge CLK) (!ctrl && (A == 4'd0) && (B == 4'd1)) |-> (Y == 4'hF)
    );

    // Adding zeros yields zero.
    check_add_zero_zero: assert property (
        @(posedge CLK) (ctrl && (A == 4'd0) && (B == 4'd0)) |-> (Y == 4'd0)
    );

    // Subtracting zeros yields zero.
    check_sub_zero_zero: assert property (
        @(posedge CLK) (!ctrl && (A == 4'd0) && (B == 4'd0)) |-> (Y == 4'd0)
    );

endmodule