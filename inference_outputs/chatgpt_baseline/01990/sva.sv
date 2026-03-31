module fulladder_sva (
    input logic CLK,
    input logic RESETn,
    input logic A,
    input logic B,
    input logic Ci,
    input logic S,
    input logic Co
);
    // FullAdder sum equals 3-input XOR of A, B, Ci.
    check_fa_sum_is_xor3: assert property (
        @(posedge CLK) disable iff (!RESETn) S == (A ^ B ^ Ci)
    );
    // FullAdder carry-out equals (A&B) | (Ci&(A^B)).
    check_fa_co_is_ab_or_cixab: assert property (
        @(posedge CLK) disable iff (!RESETn) Co == ((A & B) | (Ci & (A ^ B)))
    );
    // With Ci=0, sum reduces to A^B.
    check_fa_sum_when_ci0: assert property (
        @(posedge CLK) disable iff (!RESETn) (Ci == 1'b0) |-> (S == (A ^ B))
    );
    // With Ci=0, carry is A&B.
    check_fa_co_when_ci0: assert property (
        @(posedge CLK) disable iff (!RESETn) (Ci == 1'b0) |-> (Co == (A & B))
    );
    // With Ci=1, sum is XNOR of A and B.
    check_fa_sum_when_ci1: assert property (
        @(posedge CLK) disable iff (!RESETn) (Ci == 1'b1) |-> (S == ~(A ^ B))
    );
    // With Ci=1, carry is A|B.
    check_fa_co_when_ci1: assert property (
        @(posedge CLK) disable iff (!RESETn) (Ci == 1'b1) |-> (Co == (A | B))
    );
endmodule

module mux1_sva (
    input logic CLK,
    input logic RESETn,
    input logic A,
    input logic B,
    input logic Sel,
    input logic Out
);
    // 1-bit mux implements Out = Sel ? A : B.
    check_mux1_function: assert property (
        @(posedge CLK) disable iff (!RESETn) Out == (Sel ? A : B)
    );
    // When Sel=0, Out must be B.
    check_mux1_sel0: assert property (
        @(posedge CLK) disable iff (!RESETn) (Sel == 1'b0) |-> (Out == B)
    );
    // When Sel=1, Out must be A.
    check_mux1_sel1: assert property (
        @(posedge CLK) disable iff (!RESETn) (Sel == 1'b1) |-> (Out == A)
    );
endmodule

module mux4bit_sva (
    input logic CLK,
    input logic RESETn,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Sel,
    input logic [3:0] Out
);
    // 4-bit mux implements Out = Sel ? A : B.
    check_mux4_function: assert property (
        @(posedge CLK) disable iff (!RESETn) Out == (Sel ? A : B)
    );
    // When Sel=0, Out must be B.
    check_mux4_sel0: assert property (
        @(posedge CLK) disable iff (!RESETn) (Sel == 1'b0) |-> (Out == B)
    );
    // When Sel=1, Out must be A.
    check_mux4_sel1: assert property (
        @(posedge CLK) disable iff (!RESETn) (Sel == 1'b1) |-> (Out == A)
    );
endmodule

module ripplecarryadder4bit_sva (
    input logic CLK,
    input logic RESETn,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Ci,
    input logic [3:0] S,
    input logic Co
);
    // 5-bit result equals zero-extended A+B plus Ci.
    logic [4:0] plus5;
    assign plus5 = {1'b0, A} + {1'b0, B} + {4'b0, Ci};

    // RippleCarryAdder4bit: {Co,S} equals zero-extended A+B+Ci.
    check_rca_sum5: assert property (
        @(posedge CLK) disable iff (!RESETn) {Co, S} == plus5
    );

    // Internal carry chain derived from A, B, and Ci.
    logic c0, c1, c2, c3;
    assign c0 = (A[0] & B[0]) | ((A[0] ^ B[0]) & Ci);
    assign c1 = (A[1] & B[1]) | ((A[1] ^ B[1]) & c0);
    assign c2 = (A[2] & B[2]) | ((A[2] ^ B[2]) & c1);
    assign c3 = (A[3] & B[3]) | ((A[3] ^ B[3]) & c2);

    // Bit 0 sum: A0 ^ B0 ^ Ci.
    check_rca_s0: assert property (
        @(posedge CLK) disable iff (!RESETn) S[0] == (A[0] ^ B[0] ^ Ci)
    );
    // Bit 1 sum: A1 ^ B1 ^ c0.
    check_rca_s1: assert property (
        @(posedge CLK) disable iff (!RESETn) S[1] == (A[1] ^ B[1] ^ c0)
    );
    // Bit 2 sum: A2 ^ B2 ^ c1.
    check_rca_s2: assert property (
        @(posedge CLK) disable iff (!RESETn) S[2] == (A[2] ^ B[2] ^ c1)
    );
    // Bit 3 sum: A3 ^ B3 ^ c2.
    check_rca_s3: assert property (
        @(posedge CLK) disable iff (!RESETn) S[3] == (A[3] ^ B[3] ^ c2)
    );
    // Final carry-out equals c3.
    check_rca_co: assert property (
        @(posedge CLK) disable iff (!RESETn) Co == c3
    );
endmodule

module adder4bit_sva (
    input logic CLK,
    input logic RESETn,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] S,
    input logic Co
);
    // 5-bit result equals zero-extended A+B (Ci=0 in Adder4bit).
    logic [4:0] plus5_0;
    assign plus5_0 = {1'b0, A} + {1'b0, B};

    // Adder4bit: {Co,S} equals zero-extended A+B with Ci=0.
    check_adder_sum5: assert property (
        @(posedge CLK) disable iff (!RESETn) {Co, S} == plus5_0
    );

    // Carry chain with Ci=0 for bitwise checks.
    logic c0, c1, c2, c3;
    assign c0 = (A[0] & B[0]);
    assign c1 = (A[1] & B[1]) | ((A[1] ^ B[1]) & c0);
    assign c2 = (A[2] & B[2]) | ((A[2] ^ B[2]) & c1);
    assign c3 = (A[3] & B[3]) | ((A[3] ^ B[3]) & c2);

    // Bit 0 sum: A0 ^ B0 (Ci=0).
    check_adder_s0: assert property (
        @(posedge CLK) disable iff (!RESETn) S[0] == (A[0] ^ B[0])
    );
    // Bit 1 sum: A1 ^ B1 ^ c0.
    check_adder_s1: assert property (
        @(posedge CLK) disable iff (!RESETn) S[1] == (A[1] ^ B[1] ^ c0)
    );
    // Bit 2 sum: A2 ^ B2 ^ c1.
    check_adder_s2: assert property (
        @(posedge CLK) disable iff (!RESETn) S[2] == (A[2] ^ B[2] ^ c1)
    );
    // Bit 3 sum: A3 ^ B3 ^ c2.
    check_adder_s3: assert property (
        @(posedge CLK) disable iff (!RESETn) S[3] == (A[3] ^ B[3] ^ c2)
    );
    // Carry-out equals c3.
    check_adder_co: assert property (
        @(posedge CLK) disable iff (!RESETn) Co == c3
    );
endmodule