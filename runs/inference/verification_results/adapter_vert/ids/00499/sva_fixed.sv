module shift_register_sva (
    input logic clk,
    input logic parallel_input,
    input logic parallel_load,
    input logic register,
    input logic reset,
    input logic shift_left,
    input logic shift_right,
    input logic b0,
    input logic b0000
);

property ResetSynceotid; @(posedge clk) (reset) |-> register == 4'b0000 ;endproperty
assert property (ResetSynceotid);

property LoadSynceotid; @(posedge clk) (reset) |->  (parallel_load) |-> register == parallel_input ;endproperty
assert property (LoadSynceotid);

property ShiftLefteotid; @(posedge clk) (reset) |->  ( ! (parallel_load) &&  (shift_left) ) |-> register == {register[2:0], 1'b0} ;endproperty
assert property (ShiftLefteotid);

property ShiftRighteotid; @(posedge clk) (reset) |->  ( ! (parallel_load)  && !(shift_left) &&  (shift_right) ) |-> register == {1'b0, register[3:1]} ;endproperty
assert property (ShiftRighteotid);

endmodule