module ripple_carry_adder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic cin,
    input logic [3:0] sum,
    input logic cout
);

// Sum bit 0 matches the full-adder equation.
    check_sum_bit0_equation: assert property (
        @(posedge clk) sum[0] == (A[0] ^ B[0] ^ cin)
    );

// Sum bit 1 uses the carry generated from bit 0.
    check_sum_bit1_equation: assert property (
        @(posedge clk) sum[1] == (A[1] ^ B[1] ^ carry0)
    );

// Sum bit 2 uses the carry generated from bit 1.
    check_sum_bit2_equation: assert property (
        @(posedge clk) sum[2] == (A[2] ^ B[2] ^ carry1)
    );

// Sum bit 3 uses the carry generated from bit 2.
    check_sum_bit3_equation: assert property (
        @(posedge clk) sum[3] == (A[3] ^ B[3] ^ carry2)
    );

// Carry-out matches the full-adder carry-out equation.
    check_cout_equation: assert property (
        @(posedge clk) cout == ((A[3] & B[3]) | (A[3] & carry2) | (B[3] & carry2))
    );

// All-zero inputs produce all-zero outputs.
    check_zero_inputs_zero_outputs: assert property (
        @(posedge clk) (A == 4'b0000 && B == 4'b0000 && cin == 1'b0) |-> (sum == 4'b0000 && cout == 1'b0)
    );

// Adding zero with no carry-in returns A unchanged.
    check_add_zero_to_a: assert property (
        @(posedge clk) (B == 4'b0000 && cin == 1'b0) |-> (sum == A && cout == 1'b0)
    );

// Adding zero with no carry-in returns B unchanged.
    check_add_zero_to_b: assert property (
        @(posedge clk) (A == 4'b0000 && cin == 1'b0) |-> (sum == B && cout == 1'b0)
    );

// Maximum inputs with carry-in produce 30 and carry-out.
    check_max_inputs_carry_out: assert property (
        @(posedge clk) (A == 4'hF && B == 4'hF && cin == 1'b1) |-> (sum == 4'h0 && cout == 1'b1)
    );

endmodule
