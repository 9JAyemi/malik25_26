module section2_schematic_sva (
    input logic Ldir_int,
    input logic Len_int,
    input logic N_1,
    input logic N_3,
    input logic N_4,
    input logic N_8,
    input logic Rdir_int,
    input logic Ren_int,
    input logic Z_B,
    input logic n62,
    input logic n63,
    input logic b0,
    input logic b1,
    input logic clk_in_12
);

property ClockSynceotid; @(posedge clk_in_12) (n63) &&  (Z_B) |->  (N_1) ;endproperty
assert property (ClockSynceotid);

property SyncCheckeotid; @(posedge clk_in_12) (Z_B) &&  (n62) |->  (N_3) ;endproperty
assert property (SyncCheckeotid);

property ValidDataeotid; @(posedge clk_in_12) (Ldir_int) &&  (N_8) &&  (Rdir_int) |->  (N_4) ;endproperty
assert property (ValidDataeotid);

property ValidDataeotid_2; @(posedge clk_in_12) (N_1) ||  (N_4) |->  (Len_int) ;endproperty
assert property (ValidDataeotid_2);

property ValidRuneotid; @(posedge clk_in_12) (N_4) ||  (N_3) |->  (Ren_int) ;endproperty
assert property (ValidRuneotid);

property ClockSynceotid_2; @(posedge clk_in_12) (n62) |->  (Rdir_int) != 1'b1 ;endproperty
assert property (ClockSynceotid_2);

property ClockSynceotid_3; @(posedge clk_in_12) (n63) |->  (Ldir_int) != 1'b1 ;endproperty
assert property (ClockSynceotid_3);

property SyncSafeeotid; @(posedge clk_in_12) (Z_B) |->  (N_8) != 1'b0 ;endproperty
assert property (SyncSafeeotid);

endmodule