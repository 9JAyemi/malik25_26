module Mux_3x1_bv2_sva #(parameter W=32) (
    input logic clk,
    input logic [1:0] select,
    input logic [W-1:0] ch_0,
    input logic [W-1:0] ch_1,
    input logic [W-1:0] ch_2,
    input logic [W-1:0] data_out
);
    // When select=00, output is all zeros.
    check_sel00_zero: assert property (
        @(posedge clk) disable iff (1'b0) (select == 2'b00) |-> (data_out == {W{1'b0}})
    );

    // When select=01, output equals ch_0.
    check_sel01_pass_ch0: assert property (
        @(posedge clk) disable iff (1'b0) (select == 2'b01) |-> (data_out == ch_0)
    );

    // When select=10, output equals ch_1.
    check_sel10_pass_ch1: assert property (
        @(posedge clk) disable iff (1'b0) (select == 2'b10) |-> (data_out == ch_1)
    );

    // When select=11, output equals ch_2.
    check_sel11_pass_ch2: assert property (
        @(posedge clk) disable iff (1'b0) (select == 2'b11) |-> (data_out == ch_2)
    );

    // If select stays 00, output remains stable (constant zero).
    check_stable_when_sel00: assert property (
        @(posedge clk) disable iff (1'b0) (select == 2'b00 && $stable(select)) |-> $stable(data_out)
    );

    // When selecting ch_0, changes on ch_1 do not affect output if ch_0 and select are stable.
    check_nonselected_ch1_noeffect_when_sel01: assert property (
        @(posedge clk) disable iff (1'b0) (select == 2'b01 && $stable(select) && $stable(ch_0) && $changed(ch_1)) |-> $stable(data_out)
    );

    // When selecting ch_0, changes on ch_2 do not affect output if ch_0 and select are stable.
    check_nonselected_ch2_noeffect_when_sel01: assert property (
        @(posedge clk) disable iff (1'b0) (select == 2'b01 && $stable(select) && $stable(ch_0) && $changed(ch_2)) |-> $stable(data_out)
    );

    // When selecting ch_1, changes on ch_0 do not affect output if ch_1 and select are stable.
    check_nonselected_ch0_noeffect_when_sel10: assert property (
        @(posedge clk) disable iff (1'b0) (select == 2'b10 && $stable(select) && $stable(ch_1) && $changed(ch_0)) |-> $stable(data_out)
    );

    // When selecting ch_1, changes on ch_2 do not affect output if ch_1 and select are stable.
    check_nonselected_ch2_noeffect_when_sel10: assert property (
        @(posedge clk) disable iff (1'b0) (select == 2'b10 && $stable(select) && $stable(ch_1) && $changed(ch_2)) |-> $stable(data_out)
    );

    // When selecting ch_2, changes on ch_0 do not affect output if ch_2 and select are stable.
    check_nonselected_ch0_noeffect_when_sel11: assert property (
        @(posedge clk) disable iff (1'b0) (select == 2'b11 && $stable(select) && $stable(ch_2) && $changed(ch_0)) |-> $stable(data_out)
    );

    // When selecting ch_2, changes on ch_1 do not affect output if ch_2 and select are stable.
    check_nonselected_ch1_noeffect_when_sel11: assert property (
        @(posedge clk) disable iff (1'b0) (select == 2'b11 && $stable(select) && $stable(ch_2) && $changed(ch_1)) |-> $stable(data_out)
    );
endmodule