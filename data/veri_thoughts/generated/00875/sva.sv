module Mux_3x1_b_sva #(parameter W=32) (
    input logic                     clk,
    input logic [1:0]               select,
    input logic [W-1:0]             ch_0,
    input logic [W-1:0]             ch_1,
    input logic [W-1:0]             ch_2,
    input logic [W-1:0]             data_out
);

    ///// Functional mapping checks /////
    // When select == 2'b00, data_out must equal ch_0.
    check_select_00_routes_ch0: assert property (
        @(posedge clk) (select == 2'b00) |-> (data_out == ch_0)
    );

    // When select == 2'b01, data_out must equal ch_1.
    check_select_01_routes_ch1: assert property (
        @(posedge clk) (select == 2'b01) |-> (data_out == ch_1)
    );

    // When select == 2'b10, data_out must equal ch_2.
    check_select_10_routes_ch2: assert property (
        @(posedge clk) (select == 2'b10) |-> (data_out == ch_2)
    );

    // When select == 2'b11, data_out must be zero.
    check_select_11_routes_zero: assert property (
        @(posedge clk) (select == 2'b11) |-> (data_out == {W{1'b0}})
    );

    // At every cycle, data_out must match the case decode of select.
    check_mux_function_total: assert property (
        @(posedge clk)
            ((select == 2'b00) && (data_out == ch_0)) ||
            ((select == 2'b01) && (data_out == ch_1)) ||
            ((select == 2'b10) && (data_out == ch_2)) ||
            ((select == 2'b11) && (data_out == {W{1'b0}}))
    );

    ///// Stability checks /////
    // If select and all channels are stable, data_out must be stable.
    check_output_stable_when_all_inputs_stable: assert property (
        @(posedge clk)
            $stable(select) && $stable(ch_0) && $stable(ch_1) && $stable(ch_2)
            |-> $stable(data_out)
    );

    // If select==2'b00 and both select and ch_0 are stable, data_out must be stable.
    check_nonselected_irrelevant_sel00: assert property (
        @(posedge clk)
            (select == 2'b00) && $stable(select) && $stable(ch_0)
            |-> $stable(data_out)
    );

    // If select==2'b01 and both select and ch_1 are stable, data_out must be stable.
    check_nonselected_irrelevant_sel01: assert property (
        @(posedge clk)
            (select == 2'b01) && $stable(select) && $stable(ch_1)
            |-> $stable(data_out)
    );

    // If select==2'b10 and both select and ch_2 are stable, data_out must be stable.
    check_nonselected_irrelevant_sel10: assert property (
        @(posedge clk)
            (select == 2'b10) && $stable(select) && $stable(ch_2)
            |-> $stable(data_out)
    );

    // If select==2'b11 and select is stable, data_out must be stable (zero remains zero).
    check_zero_out_stable_when_sel11: assert property (
        @(posedge clk)
            (select == 2'b11) && $stable(select)
            |-> $stable(data_out)
    );

endmodule