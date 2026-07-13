module top_module_assertions (
    input logic clk,
    input logic reset,
    input logic [1023:0] in,
    input logic [2:0] sel,
    input logic [2:0] vec,
    input logic [3:0] out,
    input logic o2,
    input logic o1,
    input logic o0
);

    // o0 reflects bit 0 of the selected 4-bit slice.
    check_o0_selected_bit: assert property (
        @(posedge clk) disable iff (reset)
        o0 == in[{sel, 2'b00}]
    );

    // o1 reflects bit 1 of the selected 4-bit slice.
    check_o1_selected_bit: assert property (
        @(posedge clk) disable iff (reset)
        o1 == in[{sel, 2'b00} + 1]
    );

    // o2 reflects bit 2 of the selected 4-bit slice.
    check_o2_selected_bit: assert property (
        @(posedge clk) disable iff (reset)
        o2 == in[{sel, 2'b00} + 2]
    );

    // vec=000 passes the selected 4-bit slice directly to out.
    check_out_passthrough_vec_000: assert property (
        @(posedge clk) disable iff (reset)
        (vec == 3'b000) |-> (out == in[{sel, 2'b00} +: 4])
    );

    // vec=001 produces the implemented shift_1 pattern.
    check_out_shift_vec_001: assert property (
        @(posedge clk) disable iff (reset)
        (vec == 3'b001) |-> (out == {o2, o1, o0, 1'b0})
    );

    // vec=010 produces the implemented shift_2 pattern.
    check_out_shift_vec_010: assert property (
        @(posedge clk) disable iff (reset)
        (vec == 3'b010) |-> (out == {o1, o0, 2'b00})
    );

    // vec=011 produces the implemented shift_3 pattern.
    check_out_shift_vec_011: assert property (
        @(posedge clk) disable iff (reset)
        (vec == 3'b011) |-> (out == {1'b0, o0, 2'b00})
    );

    // vec values with bit 2 set force out to zero.
    check_out_zero_for_vec_1xx: assert property (
        @(posedge clk) disable iff (reset)
        vec[2] |-> (out == 4'b0000)
    );

endmodule