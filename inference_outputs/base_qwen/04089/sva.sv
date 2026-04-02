module binary_adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic CIN,
    output logic [3:0] SUM,
    output logic COUT
);
    // Combinational logic, so use @(posedge clk)
    // No clock or reset signals present in the RTL

    // SUM should be the correct sum of A, B, and CIN
    sum_correct: assert property (
        @(posedge clk) disable iff (1'b0) (SUM == A + B + CIN)
    );

    // COUT should be the correct carry out of the addition
    carry_out_correct: assert property (
        @(posedge clk) disable iff (1'b0) (COUT == (A & B) | (A & CIN) | (B & CIN))
    );

    // SUM should not be greater than 4 bits
    sum_within_range: assert property (
        @(posedge clk) disable iff (1'b0) (SUM <= 4'b1111)
    );

    // COUT should be either 0 or 1
    carry_out_within_range: assert property (
        @(posedge clk) disable iff (1'b0) (COUT == 1'b0 || COUT == 1'b1)
    );

    // SUM should be the same as the sum of A and B without carry
    sum_without_carry: assert property (
        @(posedge clk) disable iff (1'b0) (SUM == A + B)
    );

    // COUT should be 1 if there is a carry from the least significant bit
    carry_out_from_lsb: assert property (
        @(posedge clk) disable iff (1'b0) (COUT == 1'b1) |-> (A[0] & B[0] & CIN)
    );

    // COUT should be 0 if there is no carry from the least significant bit
    carry_out_from_lsb_zero: assert property (
        @(posedge clk) disable iff (1'b0) (COUT == 1'b0) |-> !(A[0] & B[0] & CIN)
    );

    // SUM should be the same as the sum of A and B without carry
    sum_without_carry_2: assert property (
        @(posedge clk) disable iff (1'b0) (SUM == A + B)
    );

    // COUT should be 1 if there is a carry from the most significant bit
    carry_out_from_msb: assert property (
        @(posedge clk) disable iff (1'b0) (COUT == 1'b1) |-> (A[3] & B[3] & CIN)
    );

    // COUT should be 0 if there is no carry from the most significant bit
    carry_out_from_msb_zero: assert property (
        @(posedge clk) disable iff (1'b0) (COUT == 1'b0) |-> !(A[3] & B[3] & CIN)
    );
endmodule