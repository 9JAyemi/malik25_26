module adder4_sva (
    input logic clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic cin,
    input logic [3:0] sum,
    input logic cout
);

// Sum bit 0 matches the first full-adder stage.
    check_sum_bit0: assert property (
        @(posedge clk) sum[0] == (a[0] ^ b[0] ^ cin)
    );

// Sum bit 1 uses the carry generated from bit 0.
    check_sum_bit1: assert property (
        @(posedge clk) sum[1] == (a[1] ^ b[1] ^ fa_cout(a[0], b[0], cin))
    );

// Sum bit 2 uses the carry generated from bit 1.
    check_sum_bit2: assert property (
        @(posedge clk) sum[2] == (a[2] ^ b[2] ^ fa_cout(a[1], b[1], fa_cout(a[0], b[0], cin)))
    );

// Sum bit 3 uses the carry generated from bit 2.
    check_sum_bit3: assert property (
        @(posedge clk) sum[3] == (a[3] ^ b[3] ^ fa_cout(a[2], b[2], fa_cout(a[1], b[1], fa_cout(a[0], b[0], cin))))
    );

// Carry-out matches the final full-adder stage.
    check_cout: assert property (
        @(posedge clk) cout == fa_cout(a[3], b[3], fa_cout(a[2], b[2], fa_cout(a[1], b[1], fa_cout(a[0], b[0], cin))))
    );

// The 5-bit output matches the 4-bit sum and carry-out.
    check_full_result: assert property (
        @(posedge clk) {cout, sum} == ({1'b0, a} + {1'b0, b} + {4'b0000, cin})
    );

endmodule
