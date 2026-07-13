module up_counter_sva (
    input logic clk,
    input logic count,
    input logic rst_n,
    input logic b0000000000000000,
    input logic clk_15,
    input logic clk_16,
    input logic rst_18,
    input logic rx_18
);

property ResetSynceotid; @(posedge clk) (rst_n) |-> count == 16'b0000000000000000 ;endproperty
assert property (ResetSynceotid);

property ResetSynceotid_2; @(posedge clk) (rst_n) &&  (  clk  !=  rst_18  || clk_16  != rx_18 ) |->  clk_15 ;endproperty
assert property (ResetSynceotid_2);

property ResetSynceotid_3; @(posedge clk) (rst_n) |->  clk_15 ;endproperty
assert property (ResetSynceotid_3);

endmodule