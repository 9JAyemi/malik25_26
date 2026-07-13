module my_module_sva (
    input logic A,
    input logic TE_B,
    input logic Z,
    input logic b0,
    input logic b1,
    input logic clk_in_15
);

property ClockSynceotid; @(posedge clk_in_15) (Z) |-> (TE_B) == 1'b1 ;endproperty
assert property (ClockSynceotid);

property ClockSynceotid_2; @(posedge clk_in_15) (Z) |-> (A) == 1'b0 ;endproperty
assert property (ClockSynceotid_2);

endmodule