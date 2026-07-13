module adder_4bit_carry_sva (
    input logic clk,            // Sampling clock for combinational checks
    input logic [3:0] a,
    input logic [3:0] b,
    input logic cin,
    input logic [3:0] sum,
    input logic cout
);
    // Local carry chain derived from inputs for bit-level checks
    logic c0, c1, c2, c3;
    assign c0 = (a[0] & b[0]) | (a[0] & cin) | (b[0] & cin);
    assign c1 = (a[1] & b[1]) | ((a[1] ^ b[1]) & c0);
    assign c2 = (a[2] & b[2]) | ((a[2] ^ b[2]) & c1);
    assign c3 = (a[3] & b[3]) | ((a[3] ^ b[3]) & c2);

    // Sum/carry equals the 5-bit addition of a, b, and cin.
    check_combined_sum: assert property (
        @(posedge clk) {cout, sum} == ({1'b0, a} + {1'b0, b} + cin)
    );

    // LSB sum equals XOR of a[0], b[0], and cin.
    check_sum_bit0: assert property (
        @(posedge clk) sum[0] == (a[0] ^ b[0] ^ cin)
    );

    // Bit1 sum uses carry from bit0.
    check_sum_bit1: assert property (
        @(posedge clk) sum[1] == (a[1] ^ b[1] ^ c0)
    );

    // Bit2 sum uses carry from bit1.
    check_sum_bit2: assert property (
        @(posedge clk) sum[2] == (a[2] ^ b[2] ^ c1)
    );

    // Bit3 sum uses carry from bit2.
    check_sum_bit3: assert property (
        @(posedge clk) sum[3] == (a[3] ^ b[3] ^ c2)
    );

    // Carry-out equals carry from bit3.
    check_cout_equals_c3: assert property (
        @(posedge clk) cout == c3
    );

    // Carry-out equals MSB of 5-bit addition.
    check_cout_from_add: assert property (
        @(posedge clk) cout == (({1'b0, a} + {1'b0, b} + cin)[4])
    );

    // Sum equals low 4 bits of 5-bit addition.
    check_sum_from_add: assert property (
        @(posedge clk) sum == (({1'b0, a} + {1'b0, b} + cin)[3:0])
    );
endmodule