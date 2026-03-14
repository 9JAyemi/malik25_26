module add_sub_sva (
    input logic CLK,
    input logic RESETn,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic sub,
    input logic [3:0] result
);
    // When sub=0, result is the low 4 bits of A+B.
    check_add_when_sub0: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (!sub) |-> (result == (A + B)[3:0])
    );

    // When sub=1, result is the low 4 bits of A-B.
    check_sub_when_sub1: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (sub) |-> (result == (A - B)[3:0])
    );

    // If B==0, result equals A (both add and sub cases).
    check_result_identity_B_zero: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (B == 4'd0) |-> (result == A)
    );

    // If A==0 and add mode, result equals B.
    check_result_identity_A_zero_add: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (!sub && (A == 4'd0)) |-> (result == B)
    );

    // If A==B and sub mode, result is zero.
    check_subtraction_zero_when_equal: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (sub && (A == B)) |-> (result == 4'd0)
    );

    // If A==0 and sub mode, result equals two's complement of B (0 - B mod 16).
    check_negate_B_when_A_zero_sub: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (sub && (A == 4'd0)) |-> (result == (4'd0 - B)[3:0])
    );

    // If inputs are unchanged across cycles, result is unchanged.
    check_output_stable_on_input_stable: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (A == $past(A) && B == $past(B) && sub == $past(sub)) |-> (result == $past(result))
    );

    // If only A increments by 1 and others hold, result increments by 1 (mod 16).
    check_result_follows_A_plus1: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (A == ($past(A) + 4'd1)[3:0] && B == $past(B) && sub == $past(sub)) |-> (result == ($past(result) + 4'd1)[3:0])
    );

    // In add mode, if only B increments by 1, result increments by 1 (mod 16).
    check_result_follows_B_plus1_add: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (!sub && sub == $past(sub) && A == $past(A) && B == ($past(B) + 4'd1)[3:0]) |-> (result == ($past(result) + 4'd1)[3:0])
    );

    // In sub mode, if only B increments by 1, result decrements by 1 (mod 16).
    check_result_follows_B_plus1_sub: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (sub && sub == $past(sub) && A == $past(A) && B == ($past(B) + 4'd1)[3:0]) |-> (result == ($past(result) - 4'd1)[3:0])
    );
endmodule