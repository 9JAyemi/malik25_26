module binary_adder_sva(
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic CIN,
    input logic [3:0] S,
    input logic COUT
);

    // No RTL clock or reset exists; clk is an external sampling clock for this combinational DUT.

    function automatic logic carry0_exp(
        input logic [3:0] a,
        input logic [3:0] b,
        input logic cin
    );
        carry0_exp = (a[0] & b[0]) | (cin & (a[0] ^ b[0]));
    endfunction

    function automatic logic carry1_exp(
        input logic [3:0] a,
        input logic [3:0] b,
        input logic cin
    );
        carry1_exp = (a[1] & b[1]) | (carry0_exp(a, b, cin) & (a[1] ^ b[1]));
    endfunction

    function automatic logic carry2_exp(
        input logic [3:0] a,
        input logic [3:0] b,
        input logic cin
    );
        carry2_exp = (a[2] & b[2]) | (carry1_exp(a, b, cin) & (a[2] ^ b[2]));
    endfunction

    // Full 5-bit result matches A + B + CIN.
    check_full_add_result: assert property (
        @(posedge clk) {COUT, S} == ({1'b0, A} + {1'b0, B} + {4'b0000, CIN})
    );

    // Bit 0 sum follows the first full-adder equation.
    check_sum_bit0: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0] ^ CIN)
    );

    // Bit 1 sum uses the carry from bit 0.
    check_sum_bit1: assert property (
        @(posedge clk) S[1] == (A[1] ^ B[1] ^ carry0_exp(A, B, CIN))
    );

    // Bit 2 sum uses the carry from bit 1.
    check_sum_bit2: assert property (
        @(posedge clk) S[2] == (A[2] ^ B[2] ^ carry1_exp(A, B, CIN))
    );

    // Bit 3 sum uses the carry from bit 2.
    check_sum_bit3: assert property (
        @(posedge clk) S[3] == (A[3] ^ B[3] ^ carry2_exp(A, B, CIN))
    );

    // Final carry-out follows the last full-adder equation.
    check_final_carry: assert property (
        @(posedge clk) COUT == ((A[3] & B[3]) | (carry2_exp(A, B, CIN) & (A[3] ^ B[3])))
    );

    // Outputs stay stable when sampled inputs stay stable.
    check_outputs_stable_when_inputs_stable: assert property (
        @(posedge clk) ($stable(A) && $stable(B) && $stable(CIN)) |-> ($stable(S) && $stable(COUT))
    );

endmodule