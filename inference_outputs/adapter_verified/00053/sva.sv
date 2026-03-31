module adder_4bit_carry_sva (
    input logic clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic cin,
    input logic [3:0] sum,
    input logic cout
);

// Sum and carry match the 5-bit addition of a, b, and cin.
    check_full_add_result: assert property (
        @(posedge clk) {cout, sum} == ({1'b0, a} + {1'b0, b} + cin)
    );

// LSB sum is the XOR of a[0], b[0], and cin.
    check_sum_bit0: assert property (
        @(posedge clk) sum[0] == (a[0] ^ b[0] ^ cin)
    );

// Bit1 sum uses the carry generated from bit0.
    check_sum_bit1: assert property (
        @(posedge clk) sum[1] == (a[1] ^ b[1] ^ ((a[0] & b[0]) | (a[0] & cin) | (b[0] & cin)))
    );

// Bit2 sum uses the carry generated from bit1.
    check_sum_bit2: assert property (
        @(posedge clk) sum[2] == (a[2] ^ b[2] ^ ((a[1] & b[1]) | (a[1] & ((a[0] & b[0]) | (a[0] & cin) | (b[0] & cin))) | (b[1] & ((a[0] & b[0]) | (a[0] & cin) | (b[0] & cin)))))
    );

// Bit3 sum uses the carry generated from bit2.
    check_sum_bit3: assert property (
        @(posedge clk) sum[3] == (a[3] ^ b[3] ^ ((a[2] & b[2]) | (a[2] & ((a[1] & b[1]) | (a[1] & ((a[0] & b[0]) | (a[0] & cin) | (b[0] & cin))) | (b[1] & ((a[0] & b[0]) | (a[0] & cin) | (b[0] & cin))))) | (b[2] & ((a[1] & b[1]) | (a[1] & ((a[0] & b[0]) | (a[0] & cin) | (b[0] & cin))) | (b[1] & ((a[0] & b[0]) | (a[0] & cin) | (b[0] & cin)))))))
    );

// Carry-out is high when the 4-bit addition overflows.
    check_cout_overflow: assert property (
        @(posedge clk) cout == (({1'b0, a} + {1'b0, b} + cin) >= 5'd16)
    );

// Carry-out is low when the 4-bit addition does not overflow.
    check_cout_no_overflow: assert property (
        @(posedge clk) cout == (({1'b0, a} + {1'b0, b} + cin) < 5'd16)
    );

endmodule
