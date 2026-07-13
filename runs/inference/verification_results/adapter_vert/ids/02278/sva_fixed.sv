module grey_counter_sva (
    input logic c_delay,
    input logic clk,
    input logic led,
    input logic osc_clk,
    input logic q,
    input logic q_reg,
    input logic rstn,
    input logic b0000,
    input logic b1111,
    input logic h000000
);

property ClockSynceotid; @(posedge clk) (q) |-> (q_reg == q + 1) ; endproperty
assert property (ClockSynceotid);

property ResetSynceotid; @(posedge clk) (q) &&  (  q_reg == 4'b1111 ) |-> (q_reg == 4'b0000) ; endproperty
assert property (ResetSynceotid);

property ClockSynceotid_2; @(posedge osc_clk) (led) |-> (c_delay == 23'h000000) ; endproperty
assert property (ClockSynceotid_2);

property ClockSynceotid_3; @(posedge osc_clk) (led) &&  (  !rstn ) |-> (c_delay == 23'h000000) ; endproperty
assert property (ClockSynceotid_3);

property ClockSynceotid_4; @(posedge osc_clk) (led) &&  (  rstn ) |-> (c_delay == c_delay + 1) ; endproperty
assert property (ClockSynceotid_4);

property ClockSynceotid_5; @(posedge osc_clk) (clk) |-> (c_delay == 23'h000000) ; endproperty
assert property (ClockSynceotid_5);

property ClockSynceotid_6; @(posedge osc_clk) (clk) &&  (  !rstn ) |-> (c_delay == 23'h000000) ; endproperty
assert property (ClockSynceotid_6);

property ClockSynceotid_7; @(posedge osc_clk) (clk) &&  (  rstn ) |-> (c_delay == c_delay + 1) ; endproperty
assert property (ClockSynceotid_7);

endmodule