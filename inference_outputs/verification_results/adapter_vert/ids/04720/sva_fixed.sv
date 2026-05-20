module functional_module_sva (
    input logic B,
    input logic D,
    input logic E,
    input logic in,
    input logic out,
    input logic clk_in_12
);

property ClockSynceotid; @(posedge clk_in_12) (B) |-> (E) ;endproperty
assert property (ClockSynceotid);

property ValidIneotid; @(posedge clk_in_12) (in) |-> (out) ;endproperty
assert property (ValidIneotid);

property ValidDataeotid; @(posedge clk_in_12) (B) |-> (D) ;endproperty
assert property (ValidDataeotid);

endmodule