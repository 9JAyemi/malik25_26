module full_adder_sva (
    input logic CLK,
    input logic A,
    input logic B,
    input logic C_in,
    input logic Sum,
    input logic C_out
);
    // Sum equals three-input XOR of A, B, and C_in.
    check_sum_is_parity: assert property (
        @(posedge CLK) Sum == (A ^ B ^ C_in)
    );

    // C_out equals (A & B) | ((A ^ B) & C_in) per RTL.
    check_cout_function: assert property (
        @(posedge CLK) C_out == ((A & B) | ((A ^ B) & C_in))
    );

    // C_out equals majority(A,B,C_in).
    check_cout_is_majority: assert property (
        @(posedge CLK) C_out == ((A & B) | (A & C_in) | (B & C_in))
    );

    // When C_in is 0, Sum reduces to A ^ B.
    check_cin0_sum: assert property (
        @(posedge CLK) (C_in == 1'b0) |-> (Sum == (A ^ B))
    );

    // When C_in is 0, C_out reduces to A & B.
    check_cin0_cout: assert property (
        @(posedge CLK) (C_in == 1'b0) |-> (C_out == (A & B))
    );

    // When C_in is 1, Sum is the inversion of A ^ B.
    check_cin1_sum: assert property (
        @(posedge CLK) (C_in == 1'b1) |-> (Sum == ~(A ^ B))
    );

    // When C_in is 1, C_out reduces to A | B.
    check_cin1_cout: assert property (
        @(posedge CLK) (C_in == 1'b1) |-> (C_out == (A | B))
    );

    // When A equals B, Sum equals C_in.
    check_equal_inputs_sum: assert property (
        @(posedge CLK) (A == B) |-> (Sum == C_in)
    );

    // When A equals B, C_out equals A (same as B).
    check_equal_inputs_cout: assert property (
        @(posedge CLK) (A == B) |-> (C_out == A)
    );

    // When A != B, Sum equals ~C_in and C_out equals C_in.
    check_xor_inputs_behavior: assert property (
        @(posedge CLK) (A ^ B) |-> ( (Sum == ~C_in) && (C_out == C_in) )
    );
endmodule