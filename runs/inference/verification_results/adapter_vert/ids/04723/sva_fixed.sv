module shift_register_sva (
    input logic areset,
    input logic clk,
    input logic data,
    input logic ena,
    input logic load,
    input logic q,
    input logic shift_reg,
    input logic shifted_value,
    input logic b0,
    input logic b1
);

property ResetSynceotid; @(posedge clk) (areset) |-> shift_reg == 4'b0 ; endproperty
assert property (ResetSynceotid);

property LoadSynceotid; @(posedge clk) (areset) != 1'b1 && (load) |-> shift_reg == data ; endproperty
assert property (LoadSynceotid);

property ShiftOneotid; @(posedge clk) (areset) != 1'b1 && !(load)  && (ena) |-> shift_reg == {1'b0, shift_reg[3:1]}; endproperty
assert property (ShiftOneotid);

property ShiftSynceotid; @(posedge clk) (areset) != 1'b1 && !(load)  && !(ena) |-> shifted_value == {1'b0, shift_reg[3:1]}; endproperty
assert property (ShiftSynceotid);

property ResetSynceotid_2; @(posedge clk) (areset) |-> q == 4'b0 ; endproperty
assert property (ResetSynceotid_2);

property ValidDataeotid; @(posedge clk) (areset) != 1'b1 && (load) && (ena)  |-> q == data ; endproperty
assert property (ValidDataeotid);

property SyncCheckeotid; @(posedge clk) (areset) != 1'b1 && !(load)  && !(ena) |-> q == shifted_value; endproperty
assert property (SyncCheckeotid);

endmodule