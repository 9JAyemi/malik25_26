module dpth_addr_sva (
    input logic clk,
    input logic ld_rat,
    input logic low_sum,
    input logic m_at,
    input logic pc,
    input logic pc_at,
    input logic pc_plus_one,
    input logic rat,
    input logic rst_n,
    input logic b0,
    input logic b00000000,
    input logic b1
);

property ResetSynceotid; @(negedge clk) (rst_n) |-> rat == 8'b00000000 ;endproperty
assert property (ResetSynceotid);

property ResetSynceotid_2; @(negedge clk) (rst_n) |-> pc == 8'b00000000 ;endproperty
assert property (ResetSynceotid_2);

property ResetSynceotid_3; @(negedge clk) (rst_n) &&  (ld_rat == 1'b1) |-> rat == low_sum ;endproperty
assert property (ResetSynceotid_3);

property ResetSynceotid_4; @(negedge clk) (rst_n) &&  (ld_rat == 1'b1) |-> pc == pc_plus_one ;endproperty
assert property (ResetSynceotid_4);

property ResetSynceotid_5; @(negedge clk) (pc_at) == (1'b0) |-> m_at == pc ;endproperty
assert property (ResetSynceotid_5);

property ResetSynceotid_6; @(negedge clk) (pc_at) != 1'b0  |-> m_at == rat ;endproperty
assert property (ResetSynceotid_6);

endmodule