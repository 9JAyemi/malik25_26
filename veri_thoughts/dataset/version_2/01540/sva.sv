module twos_complement_sva (
    input logic CLK,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic [3:0] out
);
    // When A=0, out equals the concatenation {A,B,C,D}.
    check_out_concat_when_a_low: assert property (
        @(posedge CLK) (A == 1'b0) |-> (out == {A, B, C, D})
    );

    // When A=0, out[3] is 0.
    check_out_msb_zero_when_a_low: assert property (
        @(posedge CLK) (A == 1'b0) |-> (out[3] == 1'b0)
    );

    // When A=0, out[2] mirrors B.
    check_out_bit2_matches_B_when_a_low: assert property (
        @(posedge CLK) (A == 1'b0) |-> (out[2] == B)
    );

    // When A=0, out[1] mirrors C.
    check_out_bit1_matches_C_when_a_low: assert property (
        @(posedge CLK) (A == 1'b0) |-> (out[1] == C)
    );

    // When A=0, out[0] mirrors D.
    check_out_bit0_matches_D_when_a_low: assert property (
        @(posedge CLK) (A == 1'b0) |-> (out[0] == D)
    );

    // When A=1, out replicates (B&C&D) across all 4 bits.
    check_out_replication_when_a_high: assert property (
        @(posedge CLK) (A == 1'b1) |-> (out == {4{B & C & D}})
    );

    // When A=1 and B=C=D=1, out is 4'hF.
    check_out_F_when_a_high_all_ones: assert property (
        @(posedge CLK) (A & B & C & D) |-> (out == 4'hF)
    );

    // When A=1 and any of B,C,D is 0, out is 4'h0.
    check_out_zero_when_a_high_any_zero: assert property (
        @(posedge CLK) (A && !(B & C & D)) |-> (out == 4'h0)
    );

    // When A=1, out[3] equals (B&C&D).
    check_out_msb_equals_and_when_a_high: assert property (
        @(posedge CLK) (A == 1'b1) |-> (out[3] == (B & C & D))
    );

    // When A=1, out[0] equals (B&C&D).
    check_out_lsb_equals_and_when_a_high: assert property (
        @(posedge CLK) (A == 1'b1) |-> (out[0] == (B & C & D))
    );
endmodule