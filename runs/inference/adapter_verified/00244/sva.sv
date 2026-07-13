module ripple_carry_adder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic [3:0] Sum,
    input logic Cout
);

// Sum[0] matches the first half-adder XOR equation.
    check_sum_bit0_xor: assert property (
        @(posedge clk) Sum[0] == (A[0] ^ B[0] ^ Cin)
    );

// Sum[1] uses the carry generated from bit 0.
    check_sum_bit1_xor_with_c0: assert property (
        @(posedge clk) Sum[1] == (A[1] ^ B[1] ^ c0)
    );

// Sum[2] uses the carry generated from bit 1.
    check_sum_bit2_xor_with_c1: assert property (
        @(posedge clk) Sum[2] == (A[2] ^ B[2] ^ c1)
    );

// Sum[3] uses the carry generated from bit 2.
    check_sum_bit3_xor_with_c2: assert property (
        @(posedge clk) Sum[3] == (A[3] ^ B[3] ^ c2)
    );

// Cout matches the carry-out equation from the final full-adder.
    check_cout_equation: assert property (
        @(posedge clk) Cout == ((A[3] & B[3]) | (A[3] & c2) | (B[3] & c2))
    );

// All-zero inputs produce all-zero outputs.
    check_zero_inputs_zero_outputs: assert property (
        @(posedge clk) (A == 4'b0000 && B == 4'b0000 && Cin == 1'b0) |-> (Sum == 4'b0000 && Cout == 1'b0)
    );

// Adding zero with Cin low returns A and no carry.
    check_add_zero_to_a: assert property (
        @(posedge clk) (B == 4'b0000 && Cin == 1'b0) |-> (Sum == A && Cout == 1'b0)
    );

// Adding zero with Cin high returns A plus one.
    check_add_one_to_a: assert property (
        @(posedge clk) (B == 4'b0000 && Cin == 1'b1) |-> (Sum == (A + 4'd1) && Cout == (A[3] & B[3]))
    );

// Adding A with Cin low returns B and no carry.
    check_add_a_to_zero: assert property (
        @(posedge clk) (A == 4'b0000 && Cin == 1'b0) |-> (Sum == B && Cout == 1'b0)
    );

// Adding A with Cin high returns B plus one.
    check_add_a_to_one: assert property (
        @(posedge clk) (A == 4'b0000 && Cin == 1'b1) |-> (Sum == (B + 4'd1) && Cout == (B[3] & A[3]))
    );

endmodule
