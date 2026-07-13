module up_down_counter_sva (
    input logic clk,
    input logic count,
    input logic count_next,
    input logic count_reg,
    input logic load,
    input logic reset,
    input logic up_down,
    input logic b0000,
    input logic b0001
);

property ResetSynceotid; @(posedge clk) (reset) |-> count_reg == 4'b0000 ;endproperty
assert property (ResetSynceotid);

property LoadSynceotid; @(posedge clk) (load) |-> count_next == count ;endproperty
assert property (LoadSynceotid);

property SyncUpeotid; @(posedge clk) ( !load ) && (  up_down ) |-> count_next == count_reg + 4'b0001 ;endproperty
assert property (SyncUpeotid);

property SyncDowneotid; @(posedge clk) ( !load ) && ( !up_down )  |-> count_next == count_reg - 4'b0001; endproperty
assert property (SyncDowneotid);

property SyncCtrleotid; @(posedge clk)  (  count  !=  count_reg  ) |->  (  !load ) && (  up_down ) ;endproperty
assert property (SyncCtrleotid);

endmodule