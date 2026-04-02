module four_bit_adder_sva (
    input logic clk,
    input logic rst_n,
    input logic [3:0] A,
    input logic [3:0] B,
    output logic [3:0] S,
    output logic COUT
);

    // Full adder logic is combinational, so we use @(posedge clk) for assertions.

    // Check that the sum S is correct for each bit position
    property check_sum;
        @(posedge clk) disable iff (!rst_n) S[0] == A[0] ^ B[0] ^ 0;
        @(posedge clk) disable iff (!rst_n) S[1] == A[1] ^ B[1] ^ C[0];
        @(posedge clk) disable iff (!rst_n) S[2] == A[2] ^ B[2] ^ C[1];
        @(posedge clk) disable iff (!rst_n) S[3] == A[3] ^ B[3] ^ C[2];
    endproperty
    assert property (check_sum) else $error("Sum calculation is incorrect");

    // Check that the carry-out COUT is correct
    property check_carry_out;
        @(posedge clk) disable iff (!rst_n) COUT == (A[3] & B[3]) | (A[3] & C[2]) | (B[3] & C[2]);
    endproperty
    assert property (check_carry_out) else $error("Carry-out calculation is incorrect");

    // Check that the carry chain is correct
    property check_carry_chain;
        @(posedge clk) disable iff (!rst_n) C[0] == (A[0] & B[0]);
        @(posedge clk) disable iff (!rst_n) C[1] == (A[1] & B[1]) | (A[1] & C[0]) | (B[1] & C[0]);
        @(posedge clk) disable iff (!rst_n) C[2] == (A[2] & B[2]) | (A[2] & C[1]) | (B[2] & C[1]);
    endproperty
    assert property (check_carry_chain) else $error("Carry chain calculation is incorrect");

    // Check that the sum and carry-out are consistent
    property check_consistency;
        @(posedge clk) disable iff (!rst_n) S[0] == A[0] ^ B[0] ^ 0 && COUT == (A[3] & B[3]) | (A[3] & C[2]) | (B[3] & C[2]);
    endproperty
    assert property (check_consistency) else $error("Sum and carry-out are inconsistent");

endmodule