module top_module_assertions (
    input logic clk,
    input logic reset,
    input logic [2:0] sel,
    input logic [3:0] data0,
    input logic [3:0] data1,
    input logic [3:0] data2,
    input logic [3:0] data3,
    input logic [3:0] data4,
    input logic [3:0] data5,
    input logic d,
    input logic [11:0] out
);

    // Upper bits are zero because a 6-bit RHS is assigned into 12-bit out.
    check_out_upper_padding_zero: assert property (
        @(posedge clk) disable iff (!reset) out[11:6] == 6'b000000
    );

    // The decoder path is constant zero, so this output slice is always zero.
    check_mux_slice_zero: assert property (
        @(posedge clk) disable iff (!reset) out[5:2] == 4'b0000
    );

    // Active-low reset forces the full output to its reset value.
    check_reset_forces_full_output: assert property (
        @(posedge clk) !reset |-> (out == 12'b000000000001)
    );

    // After any active clock, the q and q_bar bits remain complementary.
    check_low_bits_remain_complementary: assert property (
        @(posedge clk) disable iff (!reset) 1'b1 |=> (out[0] == ~out[1])
    );

    // On the first sampled cycle after reset rises, the sampled output is still the reset value.
    check_reset_release_sampled_output: assert property (
        @(posedge clk) (!reset) ##1 reset |-> (out == 12'b000000000001)
    );

endmodule