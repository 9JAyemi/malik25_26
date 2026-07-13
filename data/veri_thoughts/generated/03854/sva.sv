module ripple_carry_adder_sva (
    input logic clk,
    input logic COUT,
    input logic [3:0] SUM,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic CIN
);

    // RTL is combinational with no reset; clk is a sampling clock for SVA.
    function automatic logic carry_maj (
        input logic a,
        input logic b,
        input logic cin
    );
        carry_maj = (a & b) | (a & cin) | (b & cin);
    endfunction

    // The 5-bit result must equal A + B + CIN.
    check_total_sum: assert property (
        @(posedge clk) disable iff (1'b0)
        ({COUT, SUM} == ({1'b0, A} + {1'b0, B} + {4'b0000, CIN}))
    );

    // Bit 0 sum matches the first full adder.
    check_sum_bit0_function: assert property (
        @(posedge clk) disable iff (1'b0)
        (SUM[0] == (A[0] ^ B[0] ^ CIN))
    );

    // Bit 1 sum uses the carry from bit 0.
    check_sum_bit1_ripple: assert property (
        @(posedge clk) disable iff (1'b0)
        (SUM[1] == (A[1] ^ B[1] ^ carry_maj(A[0], B[0], CIN)))
    );

    // Bit 2 sum uses the carry from bit 1.
    check_sum_bit2_ripple: assert property (
        @(posedge clk) disable iff (1'b0)
        (SUM[2] == (A[2] ^ B[2] ^ carry_maj(A[1], B[1], carry_maj(A[0], B[0], CIN))))
    );

    // Bit 3 sum uses the carry from bit 2.
    check_sum_bit3_ripple: assert property (
        @(posedge clk) disable iff (1'b0)
        (SUM[3] == (A[3] ^ B[3] ^ carry_maj(A[2], B[2], carry_maj(A[1], B[1], carry_maj(A[0], B[0], CIN)))))
    );

    // Final carry-out matches the last full adder carry.
    check_cout_ripple: assert property (
        @(posedge clk) disable iff (1'b0)
        (COUT == carry_maj(A[3], B[3], carry_maj(A[2], B[2], carry_maj(A[1], B[1], carry_maj(A[0], B[0], CIN)))))
    );

    // Stable inputs must produce stable outputs.
    check_combinational_stability: assert property (
        @(posedge clk) disable iff (1'b0)
        $stable({A, B, CIN}) |-> $stable({COUT, SUM})
    );

    // Adding zero on B with no carry-in must pass A through.
    check_add_zero_right: assert property (
        @(posedge clk) disable iff (1'b0)
        ((B == 4'b0000) && (CIN == 1'b0)) |-> ({COUT, SUM} == {1'b0, A})
    );

    // Adding zero on A with no carry-in must pass B through.
    check_add_zero_left: assert property (
        @(posedge clk) disable iff (1'b0)
        ((A == 4'b0000) && (CIN == 1'b0)) |-> ({COUT, SUM} == {1'b0, B})
    );

    // Zero operands must propagate CIN into the result.
    check_cin_only_case: assert property (
        @(posedge clk) disable iff (1'b0)
        ((A == 4'b0000) && (B == 4'b0000)) |-> ({COUT, SUM} == {4'b0000, CIN})
    );

endmodule