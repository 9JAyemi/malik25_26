module alu_behav_new_sva (
    input logic        clk,
    input logic [15:0] Y,
    input logic [15:0] flags,
    input logic [15:0] A,
    input logic [15:0] B,
    input logic [3:0]  sel
);

    // Unused flag bits are always low.
    check_reserved_flags_zero: assert property (
        @(posedge clk)
        (flags[15:8] == 8'h00) &&
        (flags[4:3]  == 2'b00) &&
        (flags[1]    == 1'b0)
    );

    // XOR selects A ^ B and clears all flags.
    check_xor_result: assert property (
        @(posedge clk)
        (sel == 4'b0011) |-> ((Y == (A ^ B)) && (flags == 16'h0000))
    );

    // AND selects A & B and clears all flags.
    check_and_result: assert property (
        @(posedge clk)
        (sel == 4'b0001) |-> ((Y == (A & B)) && (flags == 16'h0000))
    );

    // OR selects A | B and clears all flags.
    check_or_result: assert property (
        @(posedge clk)
        (sel == 4'b0010) |-> ((Y == (A | B)) && (flags == 16'h0000))
    );

    // ADD drives Y with the sum and flags[0] with the carry-out.
    check_add_result_and_carry: assert property (
        @(posedge clk)
        (sel == 4'b0101) |-> (({flags[0], Y} == ({1'b0, A} + {1'b0, B})) &&
                              (flags[2] == 1'b0) &&
                              (flags[6] == 1'b0) &&
                              (flags[7] == 1'b0))
    );

    // ADD sets overflow exactly per the RTL condition.
    check_add_overflow: assert property (
        @(posedge clk)
        (sel == 4'b0101) |-> (flags[5] ==
                              (((A[15] == 1'b0) && (B[15] == 1'b0) && ($signed(A + B) < 0)) ||
                               ((A[15] == 1'b1) && (B[15] == 1'b1) && ($signed(A + B) >= 0))))
    );

    // SUB drives Y with A - B and flags[0] with the carry-out.
    check_sub_result_and_carry: assert property (
        @(posedge clk)
        (sel == 4'b1001) |-> (({flags[0], Y} == ({1'b0, A} + {1'b0, ~B} + 17'h00001)) &&
                              (flags[2] == 1'b0) &&
                              (flags[6] == 1'b0) &&
                              (flags[7] == 1'b0))
    );

    // SUB sets overflow exactly per the RTL condition.
    check_sub_overflow: assert property (
        @(posedge clk)
        (sel == 4'b1001) |-> (flags[5] ==
                              (((A[15] == 1'b0) && (B[15] == 1'b1) && ($signed(A + ~B + 16'h0001) < 0)) ||
                               ((A[15] == 1'b1) && (B[15] == 1'b0) && ($signed(A + ~B + 16'h0001) >= 0))))
    );

    // Shift-left uses B and clears all flags.
    check_shift_left_result: assert property (
        @(posedge clk)
        (sel == 4'b1101) |-> ((Y == {B[14:0], 1'b0}) && (flags == 16'h0000))
    );

    // Load-upper swaps B bytes and clears all flags.
    check_load_upper_result: assert property (
        @(posedge clk)
        (sel == 4'b1111) |-> ((Y == {B[7:0], B[15:8]}) && (flags == 16'h0000))
    );

    // CMP preserves Y as A and reports compare flags from A - B.
    check_cmp_output_and_flags: assert property (
        @(posedge clk)
        (sel == 4'b1011) |-> ((Y == A) &&
                              (flags[0] == (A >= B)) &&
                              (flags[2] == (A < B)) &&
                              (flags[6] == (A == B)) &&
                              (flags[7] == (($signed(A + ~B + 16'h0001) < 0))))
    );

    // CMP sets overflow exactly per the RTL subtraction condition.
    check_cmp_overflow: assert property (
        @(posedge clk)
        (sel == 4'b1011) |-> (flags[5] ==
                              (((A[15] == 1'b0) && (B[15] == 1'b1) && ($signed(A + ~B + 16'h0001) < 0)) ||
                               ((A[15] == 1'b1) && (B[15] == 1'b0) && ($signed(A + ~B + 16'h0001) >= 0))))
    );

    // Unlisted sel values pass A through and clear all flags.
    check_default_passthrough: assert property (
        @(posedge clk)
        ((sel != 4'b0011) &&
         (sel != 4'b0001) &&
         (sel != 4'b0010) &&
         (sel != 4'b0101) &&
         (sel != 4'b1001) &&
         (sel != 4'b1011) &&
         (sel != 4'b1101) &&
         (sel != 4'b1111)) |-> ((Y == A) && (flags == 16'h0000))
    );

endmodule