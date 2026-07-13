module GeAr_N8_R1_P6_sva (
    input logic clk,         // sampling clock (RTL has no clock)
    input logic [7:0] in1,
    input logic [7:0] in2,
    input logic [8:0] res
);
    // Output equals 8-bit sum (zero-extended to 9 bits).
    check_sum_definition: assert property (
        @(posedge clk) disable iff (1'b0) res == (in1 + in2)
    );

    // MSB of result is always zero.
    check_msb_zero: assert property (
        @(posedge clk) disable iff (1'b0) res[8] == 1'b0
    );

    // Lower byte matches truncated 8-bit sum.
    check_lower_byte_match: assert property (
        @(posedge clk) disable iff (1'b0) res[7:0] == (in1 + in2)
    );

    // Commutativity preserved: swapping operands yields same result.
    check_commutative_sum: assert property (
        @(posedge clk) disable iff (1'b0) res == (in2 + in1)
    );

    // Adding zero on in2 returns in1 in the lower byte and zero MSB.
    check_add_zero_in2: assert property (
        @(posedge clk) disable iff (1'b0) (in2 == 8'd0) |-> (res[7:0] == in1 && res[8] == 1'b0)
    );

    // Adding zero on in1 returns in2 in the lower byte and zero MSB.
    check_add_zero_in1: assert property (
        @(posedge clk) disable iff (1'b0) (in1 == 8'd0) |-> (res[7:0] == in2 && res[8] == 1'b0)
    );

    // If inputs are stable across a cycle, output is stable (pure combinational).
    check_stability_when_inputs_stable: assert property (
        @(posedge clk) disable iff (1'b0) ($stable(in1) && $stable(in2)) |-> $stable(res)
    );

    // Output numeric range is 0..255.
    check_output_range: assert property (
        @(posedge clk) disable iff (1'b0) res <= 9'd255
    );

    // LSB equals XOR of input LSBs (no carry-in).
    check_lsb_xor: assert property (
        @(posedge clk) disable iff (1'b0) res[0] == (in1[0] ^ in2[0])
    );
endmodule