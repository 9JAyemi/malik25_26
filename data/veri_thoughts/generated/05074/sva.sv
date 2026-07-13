module top_module_sva (
    input logic [3:0] in,
    input logic a,
    input logic b,
    input logic clk,
    input logic reset,
    input logic final_out
);

    logic [1:0] and1, and2, or1, or2, xor1, xor2;
    logic out_and, out_or, out_xor;
    logic xor_gate_out;

    assign and1 = in[0] & in[1];
    assign and2 = in[2] & in[3];
    assign or1  = in[0] | in[1];
    assign or2  = in[2] | in[3];
    assign xor1 = in[0] ^ in[1];
    assign xor2 = in[2] ^ in[3];

    assign out_and = and1 & and2;
    assign out_or  = or1 | or2;
    assign out_xor = xor1 ^ xor2;

    assign xor_gate_out = a ^ b;

    // A sampled reset must leave final_out low on the next clock.
    check_reset_clears_on_next_clock: assert property (
        @(posedge clk) reset |=> (final_out == 1'b0)
    );

    // On the first clock after reset deasserts, final_out is still low.
    check_reset_release_starts_low: assert property (
        @(posedge clk) reset ##1 !reset |-> (final_out == 1'b0)
    );

    // Without reset, final_out updates to the previous cycle's combinational result.
    check_registered_function_update: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (final_out == $past((out_and & out_or) ^ (out_xor ^ xor_gate_out)))
    );

    // With all in bits low and a^b low, the next final_out is 0.
    check_zero_inputs_equal_ab: assert property (
        @(posedge clk) disable iff (reset)
        ((in == 4'b0000) && ((a ^ b) == 1'b0)) |=> (final_out == 1'b0)
    );

    // With all in bits low and a^b high, the next final_out is 1.
    check_zero_inputs_diff_ab: assert property (
        @(posedge clk) disable iff (reset)
        ((in == 4'b0000) && ((a ^ b) == 1'b1)) |=> (final_out == 1'b1)
    );

    // With all in bits high and a^b low, the next final_out is 1.
    check_all_ones_equal_ab: assert property (
        @(posedge clk) disable iff (reset)
        ((in == 4'b1111) && ((a ^ b) == 1'b0)) |=> (final_out == 1'b1)
    );

    // With all in bits high and a^b high, the next final_out is 0.
    check_all_ones_diff_ab: assert property (
        @(posedge clk) disable iff (reset)
        ((in == 4'b1111) && ((a ^ b) == 1'b1)) |=> (final_out == 1'b0)
    );

    // With exactly one in bit high and a^b low, the next final_out is 1.
    check_onehot_inputs_equal_ab: assert property (
        @(posedge clk) disable iff (reset)
        (((in == 4'b0001) || (in == 4'b0010) || (in == 4'b0100) || (in == 4'b1000)) &&
         ((a ^ b) == 1'b0)) |=> (final_out == 1'b1)
    );

    // With exactly one in bit high and a^b high, the next final_out is 0.
    check_onehot_inputs_diff_ab: assert property (
        @(posedge clk) disable iff (reset)
        (((in == 4'b0001) || (in == 4'b0010) || (in == 4'b0100) || (in == 4'b1000)) &&
         ((a ^ b) == 1'b1)) |=> (final_out == 1'b0)
    );

endmodule