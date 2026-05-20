module sky130_fd_sc_hd__lpflow_inputiso0n_sva (
    input logic A,
    input logic SLEEP_B,
    input logic X,
    input logic b0,
    input logic b1,
    input logic clk_reset_14
);

property ResetSynceotid; @(negedge clk_reset_14) (X) == (1'b0) |-> (A) == 1'b0 && (SLEEP_B) == 1'b1 ;endproperty
assert property (ResetSynceotid);

property ResetSynceotid_2; @(negedge clk_reset_14) (X) != 1'b0 |-> (A) != 1'b0 || (SLEEP_B) != 1'b1 ;endproperty
assert property (ResetSynceotid_2);

property ResetSynceotid_3; @(negedge clk_reset_14) (X) != 1'b1 || (A) != 1'b0 || (SLEEP_B) != 1'b1 ;endproperty
assert property (ResetSynceotid_3);

endmodule