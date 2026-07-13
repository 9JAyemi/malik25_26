module butterfly_4_sva (
    input logic clk,
    input logic rst,
    input logic signed [23:0] i_0,
    input logic signed [23:0] i_1,
    input logic signed [23:0] i_2,
    input logic signed [23:0] i_3,
    input logic signed [24:0] o_0,
    input logic signed [24:0] o_1,
    input logic signed [24:0] o_2,
    input logic signed [24:0] o_3
);

    // Outputs are zero whenever reset is asserted low.
    check_reset_clears_outputs: assert property (
        @(posedge clk)
        !rst |-> ((o_0 == 25'sd0) && (o_1 == 25'sd0) && (o_2 == 25'sd0) && (o_3 == 25'sd0))
    );

    // A sampled reset-low cycle leaves outputs at zero at the next sample.
    check_reset_holds_zero_to_next_sample: assert property (
        @(posedge clk)
        !rst |=> ((o_0 == 25'sd0) && (o_1 == 25'sd0) && (o_2 == 25'sd0) && (o_3 == 25'sd0))
    );

    // o_0 registers the previous-cycle i_0 + i_3 value.
    check_o0_registers_b0: assert property (
        @(posedge clk) disable iff (!rst)
        $past(rst) |-> (o_0 == $past(i_0 + i_3))
    );

    // o_1 registers the previous-cycle i_1 + i_2 value.
    check_o1_registers_b1: assert property (
        @(posedge clk) disable iff (!rst)
        $past(rst) |-> (o_1 == $past(i_1 + i_2))
    );

    // o_2 registers the previous-cycle i_1 - i_2 value.
    check_o2_registers_b2: assert property (
        @(posedge clk) disable iff (!rst)
        $past(rst) |-> (o_2 == $past(i_1 - i_2))
    );

    // o_3 registers the previous-cycle i_0 - i_3 value.
    check_o3_registers_b3: assert property (
        @(posedge clk) disable iff (!rst)
        $past(rst) |-> (o_3 == $past(i_0 - i_3))
    );

endmodule