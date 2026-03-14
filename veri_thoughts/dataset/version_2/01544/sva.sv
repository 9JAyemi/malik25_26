module add_4bit_sva (
    input logic CLK,           // External verification clock (DUT has no clock)
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [4:0] C
);
    // Helper expressions for ripple-carry expansion based only on A and B
    let carry0 = (A[0] & B[0]);
    let carry1 = (A[1] & B[1]) | ((A[1] ^ B[1]) & carry0);
    let carry2 = (A[2] & B[2]) | ((A[2] ^ B[2]) & carry1);
    let carry3 = (A[3] & B[3]) | ((A[3] ^ B[3]) & carry2);

    ///// Functional correctness /////
    // Sum equals A+B.
    check_sum_correct: assert property (
        @(posedge CLK) C == (A + B)
    );
    // LSB is XOR of A[0] and B[0] (c_in = 0).
    check_bit0_xor: assert property (
        @(posedge CLK) C[0] == (A[0] ^ B[0])
    );
    // Bit1 equals XOR of A[1], B[1], and carry0.
    check_bit1_sum: assert property (
        @(posedge CLK) C[1] == (A[1] ^ B[1] ^ carry0)
    );
    // Bit2 equals XOR of A[2], B[2], and carry1.
    check_bit2_sum: assert property (
        @(posedge CLK) C[2] == (A[2] ^ B[2] ^ carry1)
    );
    // Bit3 equals XOR of A[3], B[3], and carry2.
    check_bit3_sum: assert property (
        @(posedge CLK) C[3] == (A[3] ^ B[3] ^ carry2)
    );
    // Carry-out equals carry3.
    check_carry_out: assert property (
        @(posedge CLK) C[4] == carry3
    );

    ///// Identities and range /////
    // Adding zero on A passes B through.
    check_zero_identity_A: assert property (
        @(posedge CLK) (A == 4'd0) |-> (C == B)
    );
    // Adding zero on B passes A through.
    check_zero_identity_B: assert property (
        @(posedge CLK) (B == 4'd0) |-> (C == A)
    );
    // Carry-out set iff sum exceeds 4'hF.
    check_carry_out_threshold: assert property (
        @(posedge CLK) C[4] == ((A + B) > 5'd15)
    );
    // Sum never exceeds 30 (15+15).
    check_output_range: assert property (
        @(posedge CLK) C <= 5'd30
    );

    ///// Combinational stability /////
    // If inputs are stable, output remains stable.
    check_stable_when_inputs_stable: assert property (
        @(posedge CLK) ($stable(A) && $stable(B)) |-> $stable(C)
    );
endmodule