module adder_4bit_carry_sva (
    input logic clk,
    input logic [3:0] sum,
    input logic cout,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic cin
);

    function automatic logic maj3 (
        input logic x,
        input logic y,
        input logic z
    );
        maj3 = (x & y) | (x & z) | (y & z);
    endfunction

    // Full 5-bit result matches the arithmetic sum.
    check_full_result: assert property (
        @(posedge clk) {cout, sum} == ({1'b0, a} + {1'b0, b} + cin)
    );

    // Sum bit 0 is the XOR of the LSB inputs and carry-in.
    check_sum_bit0: assert property (
        @(posedge clk) sum[0] == (a[0] ^ b[0] ^ cin)
    );

    // Sum bit 1 uses the carry from bit 0.
    check_sum_bit1: assert property (
        @(posedge clk) sum[1] == (a[1] ^ b[1] ^ maj3(a[0], b[0], cin))
    );

    // Sum bit 2 uses the ripple carry from bits 0 and 1.
    check_sum_bit2: assert property (
        @(posedge clk) sum[2] == (a[2] ^ b[2] ^ maj3(a[1], b[1], maj3(a[0], b[0], cin)))
    );

    // Sum bit 3 uses the ripple carry from bits 0 through 2.
    check_sum_bit3: assert property (
        @(posedge clk) sum[3] == (a[3] ^ b[3] ^ maj3(a[2], b[2], maj3(a[1], b[1], maj3(a[0], b[0], cin))))
    );

    // Carry-out is the final ripple carry from the MSB stage.
    check_cout_bit: assert property (
        @(posedge clk) cout == maj3(a[3], b[3], maj3(a[2], b[2], maj3(a[1], b[1], maj3(a[0], b[0], cin))))
    );

endmodule