module shift_register_sva (
    input logic clk,
    input logic in,
    input logic reg1,
    input logic shift_dir,
    input logic reg2,
    input logic reg3,
    input logic reg4
);

property ClockSynceotid; @(posedge clk) (shift_dir) |-> in == reg1 && reg1 == reg2 && reg2 == reg3 ; endproperty
assert property (ClockSynceotid);

property ShiftSynceotid; @(posedge clk) ( !shift_dir ) |-> reg4 == reg3 && reg3 == reg2 && reg2 == in ; endproperty
assert property (ShiftSynceotid);

property SyncIniteotid; @(posedge clk)  (  shift_dir  !=  1  &&  reg4  !=  reg3 ) |-> reg4 == reg3 && reg3 == reg2 && reg2 == reg1 ; endproperty
assert property (SyncIniteotid);

property SyncIniteotid_2; @(posedge clk)  (  reg4  !=  reg3  || reg3  !=  reg2  || reg2  !=  reg1  ||  reg1  !=  in ) |-> reg4 == reg3 && reg3 == reg2 && reg2 == in ; endproperty
assert property (SyncIniteotid_2);

endmodule