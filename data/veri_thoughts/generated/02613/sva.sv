module ripple_carry_adder_sva (
    input logic CLK,
    input logic RESETn, // external reset for property gating (DUT has no reset)
    input logic [3:0] A,
    input logic [3:0] B,
    input logic cin,
    input logic [3:0] sum,
    input logic cout
);
    ///// Arithmetic correctness /////
    // Sum+carry equals 5-bit addition of A, B, and cin.
    check_sum_cout_matches_addition: assert property (
        @(posedge CLK) disable iff (!RESETn)
        ({cout, sum} == ({1'b0, A} + {1'b0, B} + {4'b0000, cin}))
    );

    ///// Bit-level ripple relationships /////
    // LSB sum is XOR of A[0], B[0], cin.
    check_sum0_xor: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (sum[0] == (A[0] ^ B[0] ^ cin))
    );
    // sum[1] equals XOR of A[1]^B[1] with carry from bit0.
    check_sum1_xor_with_c1: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (sum[1] == ((A[1] ^ B[1]) ^ ((A[0] & B[0]) | ((A[0] ^ B[0]) & cin))))
    );
    // sum[2] equals XOR of A[2]^B[2] with carry from bit1.
    check_sum2_xor_with_c2: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (sum[2] == ((A[2] ^ B[2]) ^ (
            (A[1] & B[1]) | ((A[1] ^ B[1]) & ((A[0] & B[0]) | ((A[0] ^ B[0]) & cin)))
        )))
    );
    // sum[3] equals XOR of A[3]^B[3] with carry from bit2.
    check_sum3_xor_with_c3: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (sum[3] == ((A[3] ^ B[3]) ^ (
            (A[2] & B[2]) | ((A[2] ^ B[2]) & (
                (A[1] & B[1]) | ((A[1] ^ B[1]) & ((A[0] & B[0]) | ((A[0] ^ B[0]) & cin)))
            ))
        )))
    );
    // cout equals carry out from bit3.
    check_cout_carry4: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (cout == (
            (A[3] & B[3]) | ((A[3] ^ B[3]) & (
                (A[2] & B[2]) | ((A[2] ^ B[2]) & (
                    (A[1] & B[1]) | ((A[1] ^ B[1]) & ((A[0] & B[0]) | ((A[0] ^ B[0]) & cin)))
                ))
            ))
        ))
    );

    ///// Sanity scenarios /////
    // All zeros in => all zeros out.
    check_zero_input_result: assert property (
        @(posedge CLK) disable iff (!RESETn)
        ((A == 4'b0000) && (B == 4'b0000) && (cin == 1'b0)) |-> ((sum == 4'b0000) && (cout == 1'b0))
    );
    // With B==0 and cin==0, output equals A and no carry.
    check_pass_through_when_B_zero_and_cin_zero: assert property (
        @(posedge CLK) disable iff (!RESETn)
        ((B == 4'b0000) && (cin == 1'b0)) |-> ((sum == A) && (cout == 1'b0))
    );
    // Adding bitwise complement with cin==0 yields 0xF and no carry.
    check_complement_no_cin: assert property (
        @(posedge CLK) disable iff (!RESETn)
        ((B == ~A) && (cin == 1'b0)) |-> ((sum == 4'hF) && (cout == 1'b0))
    );
    // Adding bitwise complement with cin==1 yields 0x0 and carry.
    check_complement_with_cin: assert property (
        @(posedge CLK) disable iff (!RESETn)
        ((B == ~A) && (cin == 1'b1)) |-> ((sum == 4'h0) && (cout == 1'b1))
    );
endmodule