module shift_register_sva (
    input logic areset,
    input logic clk,
    input logic data,
    input logic ena,
    input logic load,
    input logic q,
    input logic b0000
);

property ResetSynceotid; @(posedge clk) (areset) |-> q == 4'b0000 ;endproperty
assert property (ResetSynceotid);

property LoadSynceotid; @(posedge clk) (areset) &&  (load) |-> q == data ;endproperty
assert property (LoadSynceotid);

property ValidDataeotid; @(posedge clk) (areset) &&  (!load) &&  (ena) |-> q == {q[2:0], q[3]};endproperty
assert property (ValidDataeotid);

endmodule