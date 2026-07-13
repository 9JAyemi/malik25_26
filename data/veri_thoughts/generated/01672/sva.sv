module three_bit_splitter_sva (
    input logic clk,
    input logic [2:0] in_vec,
    input logic o0,
    input logic o1,
    input logic o2
);
    // o0 equals LSB of in_vec.
    check_split_o0_maps_bit0: assert property (
        @(posedge clk) disable iff (1'b0) (o0 == in_vec[0])
    );
    // o1 equals middle bit of in_vec.
    check_split_o1_maps_bit1: assert property (
        @(posedge clk) disable iff (1'b0) (o1 == in_vec[1])
    );
    // o2 equals MSB of in_vec.
    check_split_o2_maps_bit2: assert property (
        @(posedge clk) disable iff (1'b0) (o2 == in_vec[2])
    );
endmodule

module barrel_shifter_sva (
    input logic clk,
    input logic [15:0] in,
    input logic [7:0] upper,
    input logic [7:0] lower
);
    // upper is bits [15:8] of in.
    check_upper_maps_high_byte: assert property (
        @(posedge clk) disable iff (1'b0) (upper == in[15:8])
    );
    // lower is bits [7:0] of in.
    check_lower_maps_low_byte: assert property (
        @(posedge clk) disable iff (1'b0) (lower == in[7:0])
    );
    // Concatenation of upper and lower reconstructs in.
    check_concat_reconstructs_in: assert property (
        @(posedge clk) disable iff (1'b0) ({upper, lower} == in)
    );
endmodule

module adder_8bit_sva (
    input logic clk,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] sum
);
    // sum is the 8-bit addition of a and b (wrap-around).
    check_sum_is_a_plus_b: assert property (
        @(posedge clk) disable iff (1'b0) (sum == (a + b))
    );
endmodule

module top_module_sva (
    input logic clk,
    input logic [15:0] in,
    input logic [7:0] out_sum
);
    // out_sum equals the 8-bit sum of in[15:8] and in[7:0] (wrap-around).
    check_out_sum_matches_halves_sum: assert property (
        @(posedge clk) disable iff (1'b0) (out_sum == (in[15:8] + in[7:0]))
    );
endmodule