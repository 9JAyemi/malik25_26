module full_adder_4bit_sva #(
    parameter int DW = 4
) (
    input  logic                 CLK,
    input  logic                 RESETn,
    input  logic [DW-1:0]        A,
    input  logic [DW-1:0]        B,
    input  logic [DW-1:0]        C_in,
    input  logic [DW-1:0]        S,
    input  logic [DW-1:0]        C_out
);
    ///// Functional equivalence (vector) /////
    // Sum output equals bitwise XOR of inputs.
    check_sum_is_xor: assert property (
        @(posedge CLK) disable iff (!RESETn) S == (A ^ B ^ C_in)
    );
    // Carry output equals bitwise majority of inputs.
    check_carry_is_majority: assert property (
        @(posedge CLK) disable iff (!RESETn) C_out == ((A & B) | (B & C_in) | (C_in & A))
    );

    ///// Combinational sanity /////
    // If inputs are stable cycle-to-cycle, outputs are stable too.
    combinational_stability: assert property (
        @(posedge CLK) disable iff (!RESETn) ($stable(A) && $stable(B) && $stable(C_in)) |=> ($stable(S) && $stable(C_out))
    );
    // All-zero inputs produce all-zero outputs.
    vector_zero_identity: assert property (
        @(posedge CLK) disable iff (!RESETn) ((A == '0) && (B == '0) && (C_in == '0)) |=> ((S == '0) && (C_out == '0))
    );
    // If all three input vectors are equal, S is zero and C_out equals that vector.
    vector_equal_inputs: assert property (
        @(posedge CLK) disable iff (!RESETn) ((A == B) && (B == C_in)) |=> ((S == '0) && (C_out == A))
    );

    ///// Bit-level properties /////
    genvar i;
    generate
        for (i = 0; i < DW; i++) begin : gen_bit_checks
            // With C_in=1, S is XNOR(A,B) and C_out is OR(A,B).
            cin1_behavior: assert property (
                @(posedge CLK) disable iff (!RESETn) (C_in[i] == 1'b1) |=> ((S[i] == ~(A[i] ^ B[i])) && (C_out[i] == (A[i] | B[i])))
            );
            // With C_in=0, S is XOR(A,B) and C_out is AND(A,B).
            cin0_behavior: assert property (
                @(posedge CLK) disable iff (!RESETn) (C_in[i] == 1'b0) |=> ((S[i] == (A[i] ^ B[i])) && (C_out[i] == (A[i] & B[i])))
            );
            // Per bit, arithmetic balance: A+B+C_in equals S + 2*C_out.
            check_weighted_sum: assert property (
                @(posedge CLK) disable iff (!RESETn) (A[i] + B[i] + C_in[i]) == (S[i] + (C_out[i] << 1))
            );
            // If exactly one input is 1, then S=1 and C_out=0.
            one_of_three: assert property (
                @(posedge CLK) disable iff (!RESETn) ((A[i] + B[i] + C_in[i]) == 2'd1) |=> ((S[i] == 1'b1) && (C_out[i] == 1'b0))
            );
            // If exactly two inputs are 1, then S=0 and C_out=1.
            two_of_three: assert property (
                @(posedge CLK) disable iff (!RESETn) ((A[i] + B[i] + C_in[i]) == 2'd2) |=> ((S[i] == 1'b0) && (C_out[i] == 1'b1))
            );
            // If all three inputs are 1, then S=1 and C_out=1.
            three_of_three: assert property (
                @(posedge CLK) disable iff (!RESETn) ((A[i] & B[i] & C_in[i]) == 1'b1) |=> ((S[i] == 1'b1) && (C_out[i] == 1'b1))
            );
            // If all three inputs are 0, then S=0 and C_out=0.
            zero_of_three: assert property (
                @(posedge CLK) disable iff (!RESETn) ((A[i] | B[i] | C_in[i]) == 1'b0) |=> ((S[i] == 1'b0) && (C_out[i] == 1'b0))
            );
        end
    endgenerate
endmodule