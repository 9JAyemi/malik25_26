module my_module_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic X,
    input logic and0_out,
    input logic or0_out_X,
    input logic clk_in_17
);

property ClockSynceotid; @(posedge clk_in_17) (and0_out) == (A1) && (A2) ;endproperty
assert property (ClockSynceotid);

property ValidSynceotid; @(posedge clk_in_17) (or0_out_X) == (and0_out) || (C1) || (B1) ;endproperty
assert property (ValidSynceotid);

property ValidXeotid; @(posedge clk_in_17) (X) == (or0_out_X) ;endproperty
assert property (ValidXeotid);

endmodule