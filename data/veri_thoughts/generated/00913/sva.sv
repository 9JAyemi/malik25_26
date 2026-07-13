module top_module_assertions (
    input logic clk,
    input logic reset,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic ctrl,
    input logic [3:0] out_adder,
    input logic [2:0] out_comparator
);
    // When ctrl=0 the 4-bit sum is selected to out_adder.
    check_mux_ctrl0_out_adder_sum: assert property (
        @(posedge clk) disable iff (reset) (!ctrl) |-> (out_adder == (a + b)[3:0])
    );

    // When ctrl=0 the low 3 bits of the sum drive out_comparator.
    check_mux_ctrl0_out_comp_sum_low3: assert property (
        @(posedge clk) disable iff (reset) (!ctrl) |-> (out_comparator == (a + b)[2:0])
    );

    // When ctrl=1 out_adder is {1'b0, comparator_code}.
    check_mux_ctrl1_out_adder_comp_packed: assert property (
        @(posedge clk) disable iff (reset) (ctrl) |-> (out_adder == {1'b0, ((a > b) ? 3'b100 : (a == b) ? 3'b010 : 3'b001)})
    );

    // When ctrl=1 out_comparator equals comparator_code.
    check_mux_ctrl1_out_comp_code: assert property (
        @(posedge clk) disable iff (reset) (ctrl) |-> (out_comparator == ((a > b) ? 3'b100 : (a == b) ? 3'b010 : 3'b001))
    );

    // Low 3 bits of out_adder always equal out_comparator.
    check_low3_consistency: assert property (
        @(posedge clk) disable iff (reset) (out_adder[2:0] == out_comparator)
    );

    // When ctrl=1 the MSB of out_adder is forced to 0 by the mux.
    check_msb_zero_when_ctrl1: assert property (
        @(posedge clk) disable iff (reset) (ctrl) |-> (out_adder[3] == 1'b0)
    );

    // When ctrl=0 the MSB of out_adder equals the MSB of (a+b).
    check_msb_matches_sum_when_ctrl0: assert property (
        @(posedge clk) disable iff (reset) (!ctrl) |-> (out_adder[3] == (a + b)[3])
    );

    // out_adder matches the ctrl-based spec using out_comparator when ctrl=1.
    check_out_adder_matches_ctrl_based_spec: assert property (
        @(posedge clk) disable iff (reset) (out_adder == (ctrl ? {1'b0, out_comparator} : (a + b)[3:0]))
    );

    // When ctrl=1 the comparator encoding is one-hot.
    check_comp_onehot_when_ctrl1: assert property (
        @(posedge clk) disable iff (reset) (ctrl) |-> $onehot(out_comparator)
    );
endmodule