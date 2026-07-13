module rotation_module_sva (
    input logic clk,
    input logic data,
    input logic in,
    input logic load,
    input logic out,
    input logic reset,
    input logic select,
    input logic b0,
    input logic b1
);

property ResetSynceotid; @(posedge clk) (reset) |-> out == 4'b0 ;endproperty
assert property (ResetSynceotid);

property LoadSynceotid; @(posedge clk) (reset) != 1'b1 && (load) |-> out == data[3:0] ;endproperty
assert property (LoadSynceotid);

property ValidDataeotid; @(posedge clk) (reset) != 1'b1 && !(load)  && (select) |-> out == {in[2:0], in[3]} ;endproperty
assert property (ValidDataeotid);

property ValidDataeotid_2; @(posedge clk) (reset) != 1'b1 && !(load)  && !(select)  |-> out == {in[0], in[3:1]} ;endproperty
assert property (ValidDataeotid_2);

endmodule