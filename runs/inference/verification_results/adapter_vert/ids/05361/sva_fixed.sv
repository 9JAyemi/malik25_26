module vga_color_generator_sva (
    input logic clk,
    input logic h_count,
    input logic rst,
    input logic v_count,
    input logic vsync,
    input logic h0
);

property ResetSynceotid; @(posedge clk) (rst) |-> h_count == 10'h0 && v_count == 10'h0 ;endproperty
assert property (ResetSynceotid);

property SyncRiseeotid; @(posedge clk) (rst) |-> (h_count) &&  (vsync == 0) &&  (v_count) ;endproperty
assert property (SyncRiseeotid);

property SyncReseteotid; @(posedge clk) (rst) |-> (h_count) &&  (vsync == 0) &&  (v_count == 524) ;endproperty
assert property (SyncReseteotid);

property SyncSafeeotid; @(posedge clk) (rst) &&  (h_count) &&  (vsync == 0) &&  (v_count) ;endproperty
assert property (SyncSafeeotid);

property SyncSafeeotid_2; @(posedge clk) (rst) |-> (h_count) &&  (vsync == 0) &&  (v_count) ;endproperty
assert property (SyncSafeeotid_2);

property SyncSafeeotid_3; @(posedge clk) (rst) |-> (h_count) &&  (vsync == 0) &&  (v_count) ;endproperty
assert property (SyncSafeeotid_3);

property SyncSafeeotid_4; @(posedge clk) (rst) |-> (h_count) &&  (vsync == 0) &&  (v_count) ;endproperty
assert property (SyncSafeeotid_4);

property SyncSafeeotid_5; @(posedge clk) (rst) |-> (h_count) &&  (vsync == 0) &&  (v_count) ;endproperty
assert property (SyncSafeeotid_5);

property SyncSafeeotid_6; @(posedge clk) (rst) |-> (h_count) &&  (vsync == 0) &&  (v_count) ;endproperty
assert property (SyncSafeeotid_6);

property SyncSafeeotid_7; @(posedge clk) (rst) |-> (h_count) &&  (vsync == 0) &&  (v_count) ;endproperty
assert property (SyncSafeeotid_7);

property SyncSafeeotid_8; @(posedge clk) (rst) |-> (h_count) &&  (vsync == 0) &&  (v_count) ;endproperty
assert property (SyncSafeeotid_8);

property SyncSafeeotid_9; @(posedge clk) (rst) |-> (h_count) &&  (vsync == 0) &&  (v_count) ;endproperty
assert property (SyncSafeeotid_9);

property SyncSafeeotid_10; @(posedge clk) (rst) |-> (h_count) &&  (vsync == 0) &&  (v_count) ;endproperty
assert property (SyncSafeeotid_10);

property SyncSafeeotid_11; @(posedge clk) (rst) |-> (h_count) &&  (vsync == 0) &&  (v_count) ;endproperty
assert property (SyncSafeeotid_11);

property SyncSafeeotid_12; @(posedge clk) (rst) |-> (h_count) &&  (vsync == 0) &&  (v_count) ;endproperty
assert property (SyncSafeeotid_12);

property SyncSafeeotid_13; @(posedge clk) (rst) |-> (h_count) &&  (vsync == 0) &&  (v_count) ;endproperty
assert property (SyncSafeeotid_13);

property SyncSafeeotid_14; @(posedge clk) (rst) |-> (h_count) &&  (vsync == 0) &&  (v_count) ;endproperty
assert property (SyncSafeeotid_14);

property SyncSafeeotid_15; @(posedge clk) (rst) |-> (h_count) &&  (vsync == 0) &&  (v_count) ;endproperty
assert property (SyncSafeeotid_15);

property SyncSafeeotid_16; @(posedge clk) (rst) |-> (h_count) &&  (vsync == 0) &&  (v_count) ;endproperty
assert property (SyncSafeeotid_16);

property SyncSafeeotid_17; @(posedge clk) (rst) |-> (h_count) &&  (vsync == 0) &&  (v_count) ;endproperty
assert property (SyncSafeeotid_17);

property SyncSafeeotid_18; @(posedge clk) (rst) |-> (h_count) &&  (vsync == 0) &&  (v_count) ;endproperty
assert property (SyncSafeeotid_18);

property SyncSafeeotid_19; @(posedge clk) (rst) |-> (h_count) &&  (vsync == 0) &&  (v_count) ;endproperty
assert property (SyncSafeeotid_19);

property SyncSafeeotid_20; @(posedge clk) (rst) |-> (h_count) &&  (vsync == 0) &&  (v_count) ;endproperty
assert property (SyncSafeeotid_20);

property SyncSafeeotid_21; @(posedge clk) (rst) |-> (h_count) &&  (vsync == 0) &&  (v_count) ;endproperty
assert property (SyncSafeeotid_21);

property SyncSafeeotid_22; @(posedge clk) (rst) |-> (h_count) &&  (vsync == 0) &&  (v_count) ;endproperty
assert property (SyncSafeeotid_22);

property SyncSafeeotid_23; @(posedge clk) (rst) |-> (h_count) &&  (vsync == 0) &&  (v_count) ;endproperty
assert property (SyncSafeeotid_23);

property SyncSafeeotid_24; @(posedge clk) (rst) |-> (h_count) &&  (vsync == 0) &&  (v_count) ;endproperty
assert property (SyncSafeeotid_24);

property SyncSafeeotid_25; @(posedge clk) (rst) |-> (h_count) &&  (vsync == 0) &&  (v_count) ;endproperty
assert property (SyncSafeeotid_25);

property SyncSafeeotid_26; @(posedge clk) (rst) |-> (h_count) &&  (vsync == 0) &&  (v_count) ;endproperty
assert property (SyncSafeeotid_26);

property SyncSafeeotid_27; @(posedge clk) (rst) |-> (h_count) &&  (vsync == 0) &&  (v_count) ;endproperty
assert property (SyncSafeeotid_27);

property SyncSafeeotid_28; @(posedge clk) (rst) |-> (h_count) &&  (vsync == 0) &&  (v_count) ;endproperty
assert property (SyncSafeeotid_28);

property SyncSafeeotid_29; @(posedge clk) (rst) |-> (h_count) &&  (vsync == 0) &&  (v_count) ;endproperty
assert property (SyncSafeeotid_29);

property SyncSafeeotid_30; @(posedge clk) (rst) |-> (h_count) &&  (vsync == 0) &&  (v_count) ;endproperty
assert property (SyncSafeeotid_30);

property SyncSafeeotid_31; @(posedge clk) (rst) |-> (h_count) &&  (vsync == 0) &&  (v_count) ;endproperty
assert property (SyncSafeeotid_31);

property SyncSafeeotid_32; @(posedge clk) (rst) |-> (h_count) &&  (vsync == 0) &&  (v_count) ;endproperty
assert property (SyncSafeeotid_32);

property SyncSafeeotid_33; @(posedge clk) (rst) |-> (h_count) &&  (vsync == 0) &&  (v_count) ;endproperty
assert property (SyncSafeeotid_33);

property SyncSafeeotid_34; @(posedge clk) (rst) |-> (h_count) &&  (vsync == 0) &&  (v_count) ;endproperty
assert property (SyncSafeeotid_34);

property SyncSafeeotid_35; @(posedge clk) (rst) |-> (h_count) &&  (vsync == 0) &&  (v_count) ;endproperty
assert property (SyncSafeeotid_35);

property SyncSafeeotid_36; @(posedge clk) (rst) |-> (h_count) &&  (vsync == 0) &&  (v_count) ;endproperty
assert property (SyncSafeeotid_36);

property SyncSafeeotid_37; @(posedge clk) (rst) |-> (h_count) &&  (vsync == 0) &&  (v_count) ;endproperty
assert property (SyncSafeeotid_37);

property SyncSafeeotid_38; @(posedge clk) (rst) |-> (h_count) &&  (vsync == 0) &&  (v_count) ;endproperty
assert property (SyncSafeeotid_38);

property SyncSafeeotid_39; @(posedge clk) (rst) |-> (h_count) &&  (vsync == 0) &&  (v_count) ;endproperty
assert property (SyncSafeeotid_39);

property SyncSafeeotid_40; @(posedge clk) (rst) |-> (h_count) &&  (vsync == 0) &&  (v_count) ;endproperty
assert property (SyncSafeeotid_40);

property SyncSafeeotid_41; @(posedge clk) (rst) |-> (h_count) &&  (vsync == 0) &&  (v_count) ;endproperty
assert property (SyncSafeeotid_41);

property SyncSafeeotid_42; @(posedge clk) (rst) |-> (h_count) &&  (vsync == 0) &&  (v_count) ;endproperty
assert property (SyncSafeeotid_42);

property SyncSafeeotid_43; @(posedge clk) (rst) |-> (h_count) &&  (vsync == 0) &&  (v_count) ;endproperty
assert property (SyncSafeeotid_43);

property SyncSafeeotid_44; @(posedge clk) (rst) |-> (h_count) &&  (vsync == 0) &&  (v_count) ;endproperty
assert property (SyncSafeeotid_44);

property SyncSafeeotid_45; @(posedge clk) (rst) |-> (h_count) &&  (vsync == 0) &&  (v_count) ;endproperty
assert property (SyncSafeeotid_45);

property SyncSafeeotid_46; @(posedge clk) (rst) |-> (h_count) &&  (vsync == 0) &&  (v_count) ;endproperty
assert property (SyncSafeeotid_46);

property SyncSafeeotid_47; @(posedge clk) (rst) |-> (h_count) &&  (vsync == 0) &&  (v_count) ;endproperty
assert property (SyncSafeeotid_47);

property SyncSafeeotid_48; @(posedge clk) (rst) |-> (h_count) &&  (vsync == 0) &&  (v_count) ;endproperty
assert property (SyncSafeeotid_48);

endmodule