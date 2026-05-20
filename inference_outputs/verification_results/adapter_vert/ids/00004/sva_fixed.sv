module mux_2to1_sva (
    input logic a,
    input logic a_and_sel,
    input logic b,
    input logic b_and_not_sel,
    input logic sel,
    input logic y,
    input logic clk_in_15
);

property ClockSynceotid; @(posedge clk_in_15) (a) |-> (y) ;endproperty
assert property (ClockSynceotid);

property ValidSynceotid; @(posedge clk_in_15) (b) |-> (y) ;endproperty
assert property (ValidSynceotid);

property ValidSynceotid_2; @(posedge clk_in_15) (sel) |-> (a_and_sel) ;endproperty
assert property (ValidSynceotid_2);

property ValidSynceotid_3; @(posedge clk_in_15) (sel) |-> (b_and_not_sel) ;endproperty
assert property (ValidSynceotid_3);

property ValidSynceotid_4; @(posedge clk_in_15) (a) &&  (b) &&  (sel) |-> (y) ;endproperty
assert property (ValidSynceotid_4);

property ValidSynceotid_5; @(posedge clk_in_15) (a) &&  (b) &&  (!sel) |-> (y) ;endproperty
assert property (ValidSynceotid_5);

property ValidSynceotid_6; @(posedge clk_in_15) (b) &&  (!a) &&  (sel) |-> (y) ;endproperty
assert property (ValidSynceotid_6);

property ValidSynceotid_7; @(posedge clk_in_15) (a) &&  (!b) &&  (!sel) |-> (y) ;endproperty
assert property (ValidSynceotid_7);

endmodule