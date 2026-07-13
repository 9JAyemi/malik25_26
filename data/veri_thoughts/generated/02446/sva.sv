module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [3:0] q,
    input logic [3:0] counter,
    input logic [3:0] mux2_input1,
    input logic [3:0] mux2_input2,
    input logic [3:0] mux4_input1,
    input logic [3:0] mux4_input2,
    input logic [3:0] mux4_input3,
    input logic [3:0] mux4_input4,
    input logic [1:0] mux4_select,
    input logic mux2_select,
    input logic [3:0] mux2_output
);
    // Counter loads zero on the cycle after reset is asserted.
    reset_counter_next_is_zero: assert property (
        @(posedge clk) reset |=> (counter == 4'b0000)
    );

    // Counter increments by 1 on consecutive non-reset cycles.
    counter_increments_no_reset: assert property (
        @(posedge clk) disable iff (reset) !$past(reset) |-> (counter == $past(counter) + 4'b0001)
    );

    // Counter wraps from 15 to 0 without reset.
    counter_wraps_at_max: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset) && ($past(counter) == 4'hF)) |-> (counter == 4'h0)
    );

    // 4:1 mux select equals counter[1:0].
    check_mux4_select_from_counter: assert property (
        @(posedge clk) disable iff (reset) mux4_select == counter[1:0]
    );

    // 2:1 mux select equals counter[3].
    check_mux2_select_from_counter: assert property (
        @(posedge clk) disable iff (reset) mux2_select == counter[3]
    );

    // mux2 input b is constant 4'hF.
    check_mux2_input2_const: assert property (
        @(posedge clk) disable iff (reset) mux2_input2 == 4'hF
    );

    // mux4 input b is constant 1.
    check_mux4_input2_const1: assert property (
        @(posedge clk) disable iff (reset) mux4_input2 == 4'h1
    );

    // mux4 input d is constant 7.
    check_mux4_input4_const7: assert property (
        @(posedge clk) disable iff (reset) mux4_input4 == 4'h7
    );

    // 2:1 mux routes input b when sel=1.
    check_mux2_sel1_routes_b: assert property (
        @(posedge clk) disable iff (reset) mux2_select |-> (mux2_output == mux2_input2)
    );

    // 2:1 mux routes input a when sel=0.
    check_mux2_sel0_routes_a: assert property (
        @(posedge clk) disable iff (reset) !mux2_select |-> (mux2_output == mux2_input1)
    );

    // 4:1 mux routes input a when sel=00.
    check_mux4_sel00_routes_a: assert property (
        @(posedge clk) disable iff (reset) (mux4_select == 2'b00) |-> (q == mux4_input1)
    );

    // 4:1 mux routes input b when sel=01.
    check_mux4_sel01_routes_b: assert property (
        @(posedge clk) disable iff (reset) (mux4_select == 2'b01) |-> (q == mux4_input2)
    );

    // 4:1 mux routes input c when sel=10.
    check_mux4_sel10_routes_c: assert property (
        @(posedge clk) disable iff (reset) (mux4_select == 2'b10) |-> (q == mux4_input3)
    );

    // 4:1 mux routes input d when sel=11.
    check_mux4_sel11_routes_d: assert property (
        @(posedge clk) disable iff (reset) (mux4_select == 2'b11) |-> (q == mux4_input4)
    );
endmodule