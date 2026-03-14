module diff_module_sva (
    input logic CLK,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic C,
    input logic [4:0] diff
);
    // When C=0, diff equals zero-extended 4-bit (A-B).
    check_diff_when_C0: assert property (
        @(posedge CLK) (C == 1'b0) |-> (diff == {1'b0, (A - B)})
    );

    // When C=1, diff equals two's complement of zero-extended 4-bit (A-B).
    check_diff_when_C1: assert property (
        @(posedge CLK) (C == 1'b1) |-> (diff == ((~{1'b0, (A - B)}) + 5'd1))
    );

    // When C=0, the MSB of diff must be 0.
    check_msb_zero_when_C0: assert property (
        @(posedge CLK) (C == 1'b0) |-> (diff[4] == 1'b0)
    );

    // For any C, if A==B then diff must be 0.
    check_zero_when_inputs_equal: assert property (
        @(posedge CLK) (A == B) |-> (diff == 5'd0)
    );

    // For any C, diff==0 implies A==B.
    check_zero_implies_inputs_equal: assert property (
        @(posedge CLK) (diff == 5'd0) |-> (A == B)
    );

    // When C=1 and A!=B, diff must be non-zero.
    check_nonzero_when_notequal_and_C1: assert property (
        @(posedge CLK) (C == 1'b1 && (A != B)) |-> (diff != 5'd0)
    );

    // When C=1 and A!=B, diff MSB must be 1.
    check_msb_one_when_C1_and_notequal: assert property (
        @(posedge CLK) (C == 1'b1 && (A != B)) |-> (diff[4] == 1'b1)
    );

    // When C rises and A,B are stable, diff is two's complement of previous diff.
    check_twos_complement_on_C_rise: assert property (
        @(posedge CLK) ($rose(C) && A == $past(A) && B == $past(B)) |-> (diff == ((~$past(diff)) + 5'd1))
    );

    // When C falls and A,B are stable, diff is two's complement of previous diff.
    check_twos_complement_on_C_fall: assert property (
        @(posedge CLK) ($fell(C) && A == $past(A) && B == $past(B)) |-> (diff == ((~$past(diff)) + 5'd1))
    );

    // When C=0 and A!=B, diff must be non-zero.
    check_nonzero_when_notequal_and_C0: assert property (
        @(posedge CLK) (C == 1'b0 && (A != B)) |-> (diff != 5'd0)
    );
endmodule