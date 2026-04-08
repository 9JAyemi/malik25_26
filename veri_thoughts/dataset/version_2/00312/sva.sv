module top_module_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic CIN,
    input logic [3:0] SUM,
    input logic COUT,
    input logic LT
);

    function automatic logic carry_bit(input logic a, input logic b, input logic cin);
        carry_bit = (a & b) | (a & cin) | (b & cin);
    endfunction

    // Sum and carry match A + B + CIN.
    check_add_result: assert property (
        @(posedge clk)
        {COUT, SUM} == ({1'b0, A} + {1'b0, B} + CIN)
    );

    // LT matches the unsigned less-than comparison.
    check_lt_equivalence: assert property (
        @(posedge clk)
        LT == (A < B)
    );

    // Bit 0 sum matches the first full-adder stage.
    check_sum_bit0: assert property (
        @(posedge clk)
        SUM[0] == (A[0] ^ B[0] ^ CIN)
    );

    // Bit 1 sum uses the carry from bit 0.
    check_sum_bit1: assert property (
        @(posedge clk)
        SUM[1] == (A[1] ^ B[1] ^ carry_bit(A[0], B[0], CIN))
    );

    // Bit 2 sum uses the carry from bit 1.
    check_sum_bit2: assert property (
        @(posedge clk)
        SUM[2] == (A[2] ^ B[2] ^ carry_bit(A[1], B[1], carry_bit(A[0], B[0], CIN)))
    );

    // Bit 3 sum uses the carry from bit 2.
    check_sum_bit3: assert property (
        @(posedge clk)
        SUM[3] == (A[3] ^ B[3] ^ carry_bit(A[2], B[2], carry_bit(A[1], B[1], carry_bit(A[0], B[0], CIN))))
    );

    // COUT matches the final full-adder carry.
    check_cout_final_stage: assert property (
        @(posedge clk)
        COUT == carry_bit(A[3], B[3], carry_bit(A[2], B[2], carry_bit(A[1], B[1], carry_bit(A[0], B[0], CIN))))
    );

    // Equal operands must not assert LT.
    check_lt_equal_case: assert property (
        @(posedge clk)
        (A == B) |-> (LT == 1'b0)
    );

    // Smaller A must assert LT.
    check_lt_less_case: assert property (
        @(posedge clk)
        (A < B) |-> (LT == 1'b1)
    );

    // Adding zero with no carry leaves A unchanged.
    check_add_identity_a: assert property (
        @(posedge clk)
        (B == 4'b0000 && CIN == 1'b0) |-> ({COUT, SUM} == {1'b0, A})
    );

    // Adding zero with no carry leaves B unchanged.
    check_add_identity_b: assert property (
        @(posedge clk)
        (A == 4'b0000 && CIN == 1'b0) |-> ({COUT, SUM} == {1'b0, B})
    );

endmodule