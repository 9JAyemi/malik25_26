module up_down_counter_sva (
    input logic clear,
    input logic clk,
    input logic count_out,
    input logic data_in,
    input logic load,
    input logic up_down,
    input logic b0,
    input logic b1
);

property ResetSynceotid; @(posedge clk) (clear) |-> count_out == 4'b0 ; endproperty
assert property (ResetSynceotid);

property LoadSynceotid; @(posedge clk) (clear) &&  (load) |-> count_out == data_in ; endproperty
assert property (LoadSynceotid);

property UpSynceotid; @(posedge clk) (clear) &&  (load) != 1  &&  (up_down) |-> count_out == count_out + 4'b1 ; endproperty
assert property (UpSynceotid);

property DownSynceotid; @(posedge clk) (clear) &&  (load) != 1  &&  (up_down) != 1  |-> count_out == count_out - 4'b1 ; endproperty
assert property (DownSynceotid);

endmodule