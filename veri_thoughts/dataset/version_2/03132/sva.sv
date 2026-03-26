module four_bit_adder_sva (
    input logic       clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic       cin,
    input logic [3:0] sum,
    input logic       cout
);

    // No DUT clock or reset; clk is the sampling clock for these checks.
    function automatic logic maj3 (
        input logic x,
        input logic y,
        input logic z
    );
        maj3 = (x & y) | (x & z) | (y & z);
    endfunction

    // Bit 0 sum matches the first full-adder XOR.
    check_bit0_sum: assert property (
        @(posedge clk) sum[0] == (a[0] ^ b[0] ^ cin)
    );

    // Bit 1 sum uses the carry generated from bit 0.
    check_bit1_sum: assert property (
        @(posedge clk) sum[1] == (a[1] ^ b[1] ^ maj3(a[0], b[0], cin))
    );

    // Bit 2 sum uses the carry generated from bit 1.
    check_bit2_sum: assert property (
        @(posedge clk) sum[2] == (a[2] ^ b[2] ^ maj3(a[1], b[1], maj3(a[0], b[0], cin)))
    );

    // Bit 3 sum uses the carry generated from bit 2.
    check_bit3_sum: assert property (
        @(posedge clk) sum[3] == (a[3] ^ b[3] ^ maj3(a[2], b[2], maj3(a[1], b[1], maj3(a[0], b[0], cin))))
    );

    // Final carry-out matches the MSB full-adder carry equation.
    check_final_carry: assert property (
        @(posedge clk) cout == maj3(a[3], b[3], maj3(a[2], b[2], maj3(a[1], b[1], maj3(a[0], b[0], cin))))
    );

    // Combined outputs equal the 5-bit arithmetic result.
    check_total_addition: assert property (
        @(posedge clk) {cout, sum} == ({1'b0, a} + {1'b0, b} + cin)
    );

    // Carry-out is high exactly when the 5-bit sum exceeds 15.
    check_cout_overflow: assert property (
        @(posedge clk) cout == (({1'b0, a} + {1'b0, b} + cin) > 5'd15)
    );

    // Stable inputs imply stable outputs at the next sample.
    check_stable_inputs_stable_outputs: assert property (
        @(posedge clk) $stable({a, b, cin}) |-> $stable({sum, cout})
    );

endmodule