module my_module_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic Y,
    input logic and0_out,
    input logic not0_out,
    input logic or0_out,
    input logic b0,
    input logic b1,
    input logic clk_in_15
);

property ClockSynceotid; @(posedge clk_in_15) (or0_out) == (1'b1) &&  (A1 == 1'b1) &&  (A2 == 1'b1) ;endproperty
assert property (ClockSynceotid);

property ValidDataeotid; @(posedge clk_in_15) (and0_out) == (1'b1) &&  (or0_out == 1'b1) &&  (B1 == 1'b1) &&  (C1 == 1'b1) ;endproperty
assert property (ValidDataeotid);

property ValidDataeotid_2; @(posedge clk_in_15) (not0_out) == (1'b0) &&  (and0_out == 1'b1) ;endproperty
assert property (ValidDataeotid_2);

property ValidDataeotid_3; @(posedge clk_in_15) (Y) == (1'b1) &&  (not0_out == 1'b0) ;endproperty
assert property (ValidDataeotid_3);

endmodule