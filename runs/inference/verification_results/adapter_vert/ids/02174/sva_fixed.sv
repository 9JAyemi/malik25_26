module zet_bitlog_sva (
    input logic cfo,
    input logic o,
    input logic ofo,
    input logic x,
    input logic b0,
    input logic clk_in_14
);

property ClockSynceotid; @(posedge clk_in_14) (x) |-> (o) ;endproperty
assert property (ClockSynceotid);

property ClockSynceotid_2; @(posedge clk_in_14) (x) |-> (cfo) == (1'b0) ;endproperty
assert property (ClockSynceotid_2);

property ClockSynceotid_3; @(posedge clk_in_14) (x) |-> (ofo) == (1'b0) ;endproperty
assert property (ClockSynceotid_3);

endmodule