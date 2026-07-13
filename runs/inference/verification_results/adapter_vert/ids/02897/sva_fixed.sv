module mux4_sva (
    input logic in0,
    input logic in1,
    input logic in2,
    input logic in3,
    input logic out,
    input logic sel0,
    input logic sel1,
    input logic clk_in_1
);

property ClockSynceotid; @(posedge clk_in_1) (sel1) && (sel0) |-> (out) == (in3) ; endproperty
assert property (ClockSynceotid);

property ValidSleotid; @(posedge clk_in_1) (sel1) && (!sel0) |-> (out) == (in2) ; endproperty
assert property (ValidSleotid);

property ValidSleotid_2; @(posedge clk_in_1) (!sel1) && (sel0) |-> (out) == (in1) ; endproperty
assert property (ValidSleotid_2);

property ValidIneotid; @(posedge clk_in_1) (!sel1) && (!sel0) |-> (out) == (in0) ; endproperty
assert property (ValidIneotid);

endmodule