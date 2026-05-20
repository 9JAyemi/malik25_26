module posManager_sva (
    input logic clear,
    input logic clk,
    input logic count_clk,
    input logic m1,
    input logic m2,
    input logic pos11,
    input logic pos12,
    input logic pos21,
    input logic pos22,
    input logic pos_diff_x,
    input logic pos_diff_y,
    input logic prev_count_clk,
    input logic prev_pos11,
    input logic b1,
    input logic b10,
    input logic b11,
    input logic prev_pos12,
    input logic prev_pos21,
    input logic prev_pos22
);

property ResetSynceotid; @(posedge clk) (clear == 2'b10 || clear == 2'b11) |-> prev_count_clk == 0 ;endproperty
assert property (ResetSynceotid);

property SyncLockeotid; @(posedge clk) (clear == 2'b10 || clear == 2'b11) |->  (prev_pos11 == pos11) && (prev_pos12 == pos12) && (prev_pos21 == pos21) && (prev_pos22 == pos22) ;endproperty
assert property (SyncLockeotid);

property SyncCheckeotid; @(posedge clk) (clear != 2'b10) && (clear != 2'b11)  |->  (prev_pos11 == pos11 + 1) && (prev_pos12 == pos12 + 1) ;endproperty
assert property (SyncCheckeotid);

property SyncCheckeotid_2; @(posedge clk) (clear != 2'b10) && (clear != 2'b11) && (m1 != 1'b1)  |->  (prev_pos11 == pos11 - 1) && (prev_pos12 == pos12 - 1) ;endproperty
assert property (SyncCheckeotid_2);

property SyncCheckeotid_3; @(posedge clk) (clear != 2'b10) && (clear != 2'b11)  |->  (prev_pos21 == pos21 + 1) && (prev_pos22 == pos22 + 1) ;endproperty
assert property (SyncCheckeotid_3);

property SyncCheckeotid_4; @(posedge clk) (clear != 2'b10) && (clear != 2'b11) && (m2 != 1'b1)  |->  (prev_pos21 == pos21 - 1) && (prev_pos22 == pos22 - 1) ;endproperty
assert property (SyncCheckeotid_4);

property SyncCheckeotid_5; @(posedge clk) (clear == 2'b10 || clear == 2'b11) |-> pos_diff_x == 0 ;endproperty
assert property (SyncCheckeotid_5);

property SyncCheckeotid_6; @(posedge clk) (clear == 2'b10 || clear == 2'b11) |-> pos_diff_y == 0 ;endproperty
assert property (SyncCheckeotid_6);

property SyncCheckeotid_7; @(posedge clk) (clear == 2'b10 || clear == 2'b11) |-> count_clk == 0 ;endproperty
assert property (SyncCheckeotid_7);

endmodule