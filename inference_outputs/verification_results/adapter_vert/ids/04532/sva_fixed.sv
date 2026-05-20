module sky130_fd_sc_ms__a21o_sva (
    input logic A1,
    input logic B1,
    input logic X,
    input logic temp1,
    input logic b1,
    input logic clk_osc_19,
    input logic temp2,
    input logic temp3,
    input logic temp4
);

property ClockSynceotid; @(posedge clk_osc_19) (A1) |-> (temp1) ; endproperty
assert property (ClockSynceotid);

property ClockSynceotid_2; @(posedge clk_osc_19) (A1) != (B1) |-> (temp2) ; endproperty
assert property (ClockSynceotid_2);

property ClockSynceotid_3; @(posedge clk_osc_19) (B1) != 1'b1  |-> (temp3) ; endproperty
assert property (ClockSynceotid_3);

property ClockSynceotid_4; @(posedge clk_osc_19) (A1)  |-> (temp4) ; endproperty
assert property (ClockSynceotid_4);

property ClockSynceotid_5; @(posedge clk_osc_19) (A1) |-> (X) == (temp1 & temp2 | temp3 & temp4) ; endproperty
assert property (ClockSynceotid_5);

endmodule