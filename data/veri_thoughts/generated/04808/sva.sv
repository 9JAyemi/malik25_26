module four_bit_adder_sva (
    input logic       clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic       cin,
    input logic [3:0] sum,
    input logic       cout
);

    function automatic logic fa_carry (
        input logic x,
        input logic y,
        input logic z
    );
        fa_carry = (x & y) | (x & z) | (y & z);
    endfunction

    // The 5-bit result must match a + b + cin.
    check_total_addition: assert property (
        @(posedge clk) {cout, sum} == ({1'b0, a} + {1'b0, b} + cin)
    );

    // Bit 0 sum matches the first full adder XOR.
    check_bit0_sum: assert property (
        @(posedge clk) sum[0] == (a[0] ^ b[0] ^ cin)
    );

    // Bit 1 sum uses the carry from bit 0.
    check_bit1_sum: assert property (
        @(posedge clk) sum[1] == (a[1] ^ b[1] ^ fa_carry(a[0], b[0], cin))
    );

    // Bit 2 sum uses the carry from bit 1.
    check_bit2_sum: assert property (
        @(posedge clk) sum[2] == (a[2] ^ b[2] ^ fa_carry(a[1], b[1], fa_carry(a[0], b[0], cin)))
    );

    // Bit 3 sum uses the carry from bit 2.
    check_bit3_sum: assert property (
        @(posedge clk) sum[3] == (a[3] ^ b[3] ^ fa_carry(a[2], b[2], fa_carry(a[1], b[1], fa_carry(a[0], b[0], cin))))
    );

    // Final carry matches the last full adder carry out.
    check_final_carry: assert property (
        @(posedge clk) cout == fa_carry(a[3], b[3], fa_carry(a[2], b[2], fa_carry(a[1], b[1], fa_carry(a[0], b[0], cin))))
    );

    // All-zero inputs produce an all-zero result.
    check_zero_inputs: assert property (
        @(posedge clk) (a == 4'b0000 && b == 4'b0000 && cin == 1'b0) |-> ({cout, sum} == 5'b00000)
    );

    // Zero on a reduces the result to b plus cin.
    check_a_zero_passthrough: assert property (
        @(posedge clk) (a == 4'b0000) |-> ({cout, sum} == ({1'b0, b} + cin))
    );

    // Zero on b reduces the result to a plus cin.
    check_b_zero_passthrough: assert property (
        @(posedge clk) (b == 4'b0000) |-> ({cout, sum} == ({1'b0, a} + cin))
    );

    // Max inputs with carry-in produce the maximum 5-bit sum.
    check_max_input_overflow: assert property (
        @(posedge clk) (a == 4'hF && b == 4'hF && cin == 1'b1) |-> ({cout, sum} == 5'h1F)
    );

    // Carry-in propagates through all stages when adding 0xF and 0x0.
    check_full_carry_propagation: assert property (
        @(posedge clk) (a == 4'hF && b == 4'h0 && cin == 1'b1) |-> ({cout, sum} == 5'h10)
    );

endmodule