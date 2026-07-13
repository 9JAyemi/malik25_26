module sky130_fd_sc_hd__mux2_1_sva (
    input logic clk,
    input logic mux_out,
    input logic rst,
    input logic b0,
    input logic b1111,
    input logic count
);

property ResetSynceotid; @(posedge clk) (rst) |-> count == 4'b0 ;endproperty
assert property (ResetSynceotid);

property ResetSynceotid_2; @(posedge clk) (rst) |->  (mux_out) == (count[0]) ;endproperty
assert property (ResetSynceotid_2);

property ResetSynceotid_3; @(posedge clk) (rst) |->  (count) != 4'b1111 ;endproperty
assert property (ResetSynceotid_3);

endmodule