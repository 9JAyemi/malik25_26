module add_sub_sva (
    input logic CLK,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic SUB,
    input logic [3:0] RESULT
);
    // RESULT equals add or subtract modulo 16 based on SUB.
    check_result_function: assert property (
        @(posedge CLK) RESULT == (SUB ? ((A - B) & 5'h0F) : ((A + B) & 5'h0F))
    );

    // When SUB=0, RESULT is A+B modulo 16.
    check_add_when_sub0: assert property (
        @(posedge CLK) (SUB == 1'b0) |-> (RESULT == ((A + B) & 5'h0F))
    );

    // When SUB=1, RESULT is A-B modulo 16.
    check_sub_when_sub1: assert property (
        @(posedge CLK) (SUB == 1'b1) |-> (RESULT == ((A - B) & 5'h0F))
    );

    // With SUB=0 and B=0, RESULT equals A.
    check_add_identity_B_zero: assert property (
        @(posedge CLK) (SUB == 1'b0 && B == 4'h0) |-> (RESULT == A)
    );

    // With SUB=0 and A=0, RESULT equals B.
    check_add_identity_A_zero: assert property (
        @(posedge CLK) (SUB == 1'b0 && A == 4'h0) |-> (RESULT == B)
    );

    // With SUB=1 and B=0, RESULT equals A.
    check_sub_identity_B_zero: assert property (
        @(posedge CLK) (SUB == 1'b1 && B == 4'h0) |-> (RESULT == A)
    );

    // With SUB=1 and A=B, RESULT is zero.
    check_sub_self_subtract_zero: assert property (
        @(posedge CLK) (SUB == 1'b1 && A == B) |-> (RESULT == 4'h0)
    );

    // With SUB=1 and A=0, RESULT equals (16 - B) modulo 16.
    check_sub_A_zero_twos_comp: assert property (
        @(posedge CLK) (SUB == 1'b1 && A == 4'h0) |-> (RESULT == ((5'd16 - B) & 5'h0F))
    );

    // With SUB=0 and B=1, RESULT is A+1 modulo 16.
    check_add_increment_by_one: assert property (
        @(posedge CLK) (SUB == 1'b0 && B == 4'h1) |-> (RESULT == ((A + 4'h1) & 5'h0F))
    );

    // With SUB=1 and B=1, RESULT is A-1 modulo 16.
    check_sub_decrement_by_one: assert property (
        @(posedge CLK) (SUB == 1'b1 && B == 4'h1) |-> (RESULT == ((A - 4'h1) & 5'h0F))
    );
endmodule