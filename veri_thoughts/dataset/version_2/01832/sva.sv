module twos_complement_sva (
    input logic CLK,
    input logic [3:0] A,
    input logic B,
    input logic [3:0] Y
);
    // When B is 1, Y is forced to zero.
    check_y_zero_when_b_high: assert property (
        @(posedge CLK) (B == 1'b1) |-> (Y == 4'b0000)
    );

    // When B is 0, Y equals two's complement of A.
    check_y_twos_complement_when_b_low: assert property (
        @(posedge CLK) (B == 1'b0) |-> (Y == (~A + 4'b0001))
    );

    // When B is 0, Y + A (mod 16) is zero.
    check_sum_zero_mod16_when_b_low: assert property (
        @(posedge CLK) (B == 1'b0) |-> ((Y + A)[3:0] == 4'h0)
    );

    // If A and B are stable across cycles, Y remains stable.
    check_y_stable_when_inputs_stable: assert property (
        @(posedge CLK) (($past(A) === A) && ($past(B) === B)) |-> (Y === $past(Y))
    );

    // Special case: when B is 0 and A is 0, Y is 0.
    check_y_zero_when_b_low_and_a_zero: assert property (
        @(posedge CLK) ((B == 1'b0) && (A == 4'h0)) |-> (Y == 4'h0)
    );

    // Special case: when B is 0 and A is 8, Y is 8 (self two's-complement point).
    check_y_equals_a_when_b_low_and_a_is_8: assert property (
        @(posedge CLK) ((B == 1'b0) && (A == 4'h8)) |-> (Y == 4'h8)
    );

    // Special case: when B is 0 and A is 15, Y is 1.
    check_y_is_1_when_b_low_and_a_is_15: assert property (
        @(posedge CLK) ((B == 1'b0) && (A == 4'hF)) |-> (Y == 4'h1)
    );

    // When B is 0 and Y is 0, A must be 0 (uniqueness of two's complement zero).
    check_a_zero_if_b_low_and_y_zero: assert property (
        @(posedge CLK) ((B == 1'b0) && (Y == 4'h0)) |-> (A == 4'h0)
    );
endmodule