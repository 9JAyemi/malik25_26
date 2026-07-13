module adder_sva (
    input logic CLK,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [7:0] S,
    input logic C_out
);

// Sum bits match the low 8 bits of A+B.
    check_sum_bits: assert property (
        @(posedge CLK) S == (A + B)
    );

// Carry-out matches the MSB of the 9-bit sum.
    check_carry_out: assert property (
        @(posedge CLK) C_out == ((A + B) >= 8'h100)
    );

// Zero plus zero produces zero with no carry.
    check_zero_plus_zero: assert property (
        @(posedge CLK) (A == 8'h00 && B == 8'h00) |-> (S == 8'h00 && C_out == 1'b0)
    );

// Adding zero on A passes B through with no carry.
    check_zero_on_a: assert property (
        @(posedge CLK) (A == 8'h00) |-> (S == B && C_out == 1'b0)
    );

// Adding zero on B passes A through with no carry.
    check_zero_on_b: assert property (
        @(posedge CLK) (B == 8'h00) |-> (S == A && C_out == 1'b0)
    );

// Maximum inputs produce 8'hFF with carry-out asserted.
    check_max_plus_max: assert property (
        @(posedge CLK) (A == 8'hFF && B == 8'hFF) |-> (S == 8'hFF && C_out == 1'b1)
    );

endmodule
