module sky130_fd_sc_lp__iso0p_sva (
    input logic A,
    input logic SLEEP,
    input logic X,
    input logic sleepn,
    input logic clk_osc_19
);

property SleepSynceotid; @(posedge clk_osc_19) (X) |-> (A) && (sleepn); endproperty
assert property (SleepSynceotid);

property SleepSynceotid_2; @(posedge clk_osc_19) (X) &&  (A) &&  (SLEEP) |-> ! (sleepn) ; endproperty
assert property (SleepSynceotid_2);

property SleepSynceotid_3; @(posedge clk_osc_19) (X) &&  (A) &&  ! (SLEEP) |->  (sleepn) ; endproperty
assert property (SleepSynceotid_3);

endmodule