module top_module_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic [2:0] a_bitwise,
    input logic [2:0] b_bitwise,
    input logic [2:0] out_sum
);

// out_sum[0] matches the RTL sum bit.
    check_out_sum_bit0: assert property (
        @(posedge clk) out_sum[0] == (a ^ b)
    );

// out_sum[1] matches the RTL sum bit.
    check_out_sum_bit1: assert property (
        @(posedge clk) out_sum[1] == (a ^ b)
    );

// out_sum[2] matches the RTL sum bit.
    check_out_sum_bit2: assert property (
        @(posedge clk) out_sum[2] == (a ^ b)
    );

endmodule
