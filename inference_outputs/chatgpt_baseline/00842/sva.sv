module ripple_carry_adder_sva (
    input logic clk,
    input logic rst_n,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [8:0] sum
);
    ///// Functional correctness /////
    // Sum equals zero-extended unsigned addition of a and b.
    check_sum_matches_addition: assert property (
        @(posedge clk) disable iff (!rst_n) sum == ({1'b0, a} + {1'b0, b})
    );

    // Carry-out bit equals MSB of the 9-bit addition.
    check_carryout_correct: assert property (
        @(posedge clk) disable iff (!rst_n) sum[8] == (({1'b0, a} + {1'b0, b})[8])
    );

    // LSB equals XOR of a[0] and b[0] (no carry-in).
    check_lsb_xor: assert property (
        @(posedge clk) disable iff (!rst_n) sum[0] == (a[0] ^ b[0])
    );

    // Sum range is limited to 0..510 for two 8-bit addends.
    check_sum_range: assert property (
        @(posedge clk) disable iff (!rst_n) sum <= 9'h1FE
    );

    ///// Identity cases /////
    // 0 + 0 = 0.
    check_zero_plus_zero: assert property (
        @(posedge clk) disable iff (!rst_n) (a == 8'h00 && b == 8'h00) |-> (sum == 9'h000)
    );

    // a + 0 = a (zero-extended).
    check_add_zero_b: assert property (
        @(posedge clk) disable iff (!rst_n) (b == 8'h00) |-> (sum == {1'b0, a})
    );

    // 0 + b = b (zero-extended).
    check_add_zero_a: assert property (
        @(posedge clk) disable iff (!rst_n) (a == 8'h00) |-> (sum == {1'b0, b})
    );

    ///// Corner cases /////
    // 0xFF + 0xFF = 0x1FE.
    check_max_plus_max: assert property (
        @(posedge clk) disable iff (!rst_n) (a == 8'hFF && b == 8'hFF) |-> (sum == 9'h1FE)
    );

    ///// Carry characterization /////
    // Carry-out equals (low 8-bit sum < a) for unsigned add without carry-in.
    check_carry_flag_via_sum_less_a: assert property (
        @(posedge clk) disable iff (!rst_n) sum[8] == (sum[7:0] < a)
    );

    // Carry-out equals (low 8-bit sum < b) for unsigned add without carry-in.
    check_carry_flag_via_sum_less_b: assert property (
        @(posedge clk) disable iff (!rst_n) sum[8] == (sum[7:0] < b)
    );

    ///// X-propagation sanity /////
    // If inputs are known, outputs must be known.
    check_no_x_when_inputs_known: assert property (
        @(posedge clk) disable iff (!rst_n) !$isunknown({a, b}) |-> !$isunknown(sum)
    );
endmodule