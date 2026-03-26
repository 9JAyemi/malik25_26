module four_bit_adder_sva (
    input logic clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic cin,
    input logic [3:0] sum,
    input logic cout
);

    function automatic logic fa_carry (
        input logic x,
        input logic y,
        input logic z
    );
        fa_carry = (x & y) | ((x ^ y) & z);
    endfunction

    // The 5-bit output must equal a + b + cin.
    check_total_addition: assert property (
        @(posedge clk) {cout, sum} == ({1'b0, a} + {1'b0, b} + {4'b0000, cin})
    );

    // Bit 0 sum matches the first full-adder XOR result.
    check_sum_bit0: assert property (
        @(posedge clk) sum[0] == (a[0] ^ b[0] ^ cin)
    );

    // Bit 1 sum uses the carry from bit 0.
    check_sum_bit1: assert property (
        @(posedge clk) sum[1] == (a[1] ^ b[1] ^ fa_carry(a[0], b[0], cin))
    );

    // Bit 2 sum uses the carry from bit 1.
    check_sum_bit2: assert property (
        @(posedge clk) sum[2] == (a[2] ^ b[2] ^ fa_carry(a[1], b[1], fa_carry(a[0], b[0], cin)))
    );

    // Bit 3 sum uses the carry from bit 2.
    check_sum_bit3: assert property (
        @(posedge clk) sum[3] == (a[3] ^ b[3] ^ fa_carry(a[2], b[2], fa_carry(a[1], b[1], fa_carry(a[0], b[0], cin))))
    );

    // Carry out matches the final full-adder carry.
    check_cout_equation: assert property (
        @(posedge clk) cout == fa_carry(a[3], b[3], fa_carry(a[2], b[2], fa_carry(a[1], b[1], fa_carry(a[0], b[0], cin))))
    );

    // Adding zero on b reduces to a plus cin.
    check_add_zero_on_b: assert property (
        @(posedge clk) (b == 4'b0000) |-> ({cout, sum} == ({1'b0, a} + {4'b0000, cin}))
    );

    // Adding zero on a reduces to b plus cin.
    check_add_zero_on_a: assert property (
        @(posedge clk) (a == 4'b0000) |-> ({cout, sum} == ({1'b0, b} + {4'b0000, cin}))
    );

    // Complementary operands with cin low produce all ones and no carry.
    check_complement_no_carryin: assert property (
        @(posedge clk) ((b == ~a) && (cin == 1'b0)) |-> ({cout, sum} == 5'b0_1111)
    );

    // Complementary operands with cin high produce zero and a carry.
    check_complement_with_carryin: assert property (
        @(posedge clk) ((b == ~a) && (cin == 1'b1)) |-> ({cout, sum} == 5'b1_0000)
    );

endmodule