module ADD4_sva (
    input logic CLK,               // Sampling clock for SVA (DUT is purely combinational; no reset)
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic [3:0] Sum,
    input logic Cout
);
    // Local expected carry chain computed from inputs
    logic c1_exp, c2_exp, c3_exp;
    assign c1_exp = (A[0] & B[0]) | ((A[0] ^ B[0]) & Cin);
    assign c2_exp = (A[1] & B[1]) | ((A[1] ^ B[1]) & c1_exp);
    assign c3_exp = (A[2] & B[2]) | ((A[2] ^ B[2]) & c2_exp);

    // Local expected sums and carry-out
    logic [3:0] sum_exp;
    logic       cout_exp;
    assign sum_exp[0] = A[0] ^ B[0] ^ Cin;
    assign sum_exp[1] = A[1] ^ B[1] ^ c1_exp;
    assign sum_exp[2] = A[2] ^ B[2] ^ c2_exp;
    assign sum_exp[3] = A[3] ^ B[3] ^ c3_exp;
    assign cout_exp   = (A[3] & B[3]) | ((A[3] ^ B[3]) & c3_exp);

    // Arithmetic reference (5-bit)
    logic [4:0] add_exp;
    assign add_exp = A + B + Cin;

    // Sum[0] matches XOR of A0,B0,Cin.
    check_sum0_xor: assert property (
        @(posedge CLK) Sum[0] == (A[0] ^ B[0] ^ Cin)
    );

    // Sum[1] matches XOR of A1,B1 and carry c1.
    check_sum1_from_c1: assert property (
        @(posedge CLK) Sum[1] == (A[1] ^ B[1] ^ c1_exp)
    );

    // Sum[2] matches XOR of A2,B2 and carry c2.
    check_sum2_from_c2: assert property (
        @(posedge CLK) Sum[2] == (A[2] ^ B[2] ^ c2_exp)
    );

    // Sum[3] matches XOR of A3,B3 and carry c3.
    check_sum3_from_c3: assert property (
        @(posedge CLK) Sum[3] == (A[3] ^ B[3] ^ c3_exp)
    );

    // Cout matches carry out from MSB stage.
    check_cout_from_c3: assert property (
        @(posedge CLK) Cout == cout_exp
    );

    // Full 5-bit result matches arithmetic addition.
    check_vector_sum_matches_add: assert property (
        @(posedge CLK) {Cout, Sum} == add_exp
    );

    // If A3=0 and B3=0 then Cout must be 0.
    check_cout_msb_00: assert property (
        @(posedge CLK) (A[3] == 1'b0 && B[3] == 1'b0) |-> (Cout == 1'b0)
    );

    // If A3=1 and B3=1 then Cout must be 1.
    check_cout_msb_11: assert property (
        @(posedge CLK) (A[3] == 1'b1 && B[3] == 1'b1) |-> (Cout == 1'b1)
    );

    // If A3!=B3 then Cout equals c3 (carry into MSB).
    check_cout_msb_mismatch_equals_c3: assert property (
        @(posedge CLK) (A[3] ^ B[3]) |-> (Cout == c3_exp)
    );

    // If A3==B3 then Sum[3] equals c3.
    check_sum3_when_msb_equal: assert property (
        @(posedge CLK) (A[3] == B[3]) |-> (Sum[3] == c3_exp)
    );

    // If A3!=B3 then Sum[3] is inverse of c3.
    check_sum3_when_msb_mismatch: assert property (
        @(posedge CLK) (A[3] ^ B[3]) |-> (Sum[3] == ~c3_exp)
    );

    // If inputs are stable across a cycle, outputs remain stable.
    check_outputs_stable_if_inputs_stable: assert property (
        @(posedge CLK) $stable({A, B, Cin}) |-> $stable({Sum, Cout})
    );
endmodule