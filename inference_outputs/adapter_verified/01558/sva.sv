module adder4bit_sva (
    input logic clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic cin,
    input logic [3:0] sum,
    input logic cout
);

// Sum bit 0 matches the full-adder XOR equation.
    check_sum_bit0: assert property (
        @(posedge clk) sum[0] == (a[0] ^ b[0] ^ cin)
    );

// Sum bit 1 uses the carry generated from bit 0.
    check_sum_bit1: assert property (
        @(posedge clk) sum[1] == (a[1] ^ b[1] ^ carry_bit0)
    );

// Sum bit 2 uses the carry generated from bit 1.
    check_sum_bit2: assert property (
        @(posedge clk) sum[2] == (a[2] ^ b[2] ^ carry_bit1)
    );

// Sum bit 3 uses the carry generated from bit 2.
    check_sum_bit3: assert property (
        @(posedge clk) sum[3] == (a[3] ^ b[3] ^ carry_bit2)
    );

// Carry-out matches the full-adder carry equation.
    check_cout: assert property (
        @(posedge clk) cout == ((a[3] & b[3]) | (a[3] & carry_bit2) | (b[3] & carry_bit2))
    );

// The 5-bit result matches the 4-bit inputs and carry-in.
    check_total_result: assert property (
        @(posedge clk) {cout, sum} == ({1'b0, a} + {1'b0, b} + {4'b0, cin})
    );

// Adding zero with no carry-in returns the other operand and no carry.
    check_add_zero_to_b: assert property (
        @(posedge clk) (b == 4'h0 && cin == 1'b0) |-> ({cout, sum} == {1'b0, a})
    );

// Adding zero with no carry-in returns the other operand and no carry.
    check_add_zero_to_a: assert property (
        @(posedge clk) (a == 4'h0 && cin == 1'b0) |-> ({cout, sum} == {1'b0, b})
    );

// All-zero inputs produce a zero result and no carry.
    check_zero_inputs: assert property (
        @(posedge clk) (a == 4'h0 && b == 4'h0 && cin == 1'b0) |-> ({cout, sum} == 5'h00)
    );

// Maximum inputs with carry-in produce 0xF and carry-out.
    check_max_inputs: assert property (
        @(posedge clk) (a == 4'hF && b == 4'hF && cin == 1'b1) |-> ({cout, sum} == 5'h1F)
    );

endmodule
