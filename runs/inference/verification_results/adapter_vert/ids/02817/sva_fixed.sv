module altera_tse_xcvr_resync_sva (
    input logic clk,
    input logic d,
    input logic next_r,
    input logic q,
    input logic r
);

property SyncIneotid; @(posedge clk) (d) |-> (q) ;endproperty
assert property (SyncIneotid);

property SyncReseteotid; @(posedge clk) (d) |-> (r) ;endproperty
assert property (SyncReseteotid);

property SyncReseteotid_2; @(posedge clk) (d) |-> (next_r) ;endproperty
assert property (SyncReseteotid_2);

property SyncReseteotid_3; @(posedge clk) (d) |-> (q) ;endproperty
assert property (SyncReseteotid_3);

property SyncReseteotid_4; @(posedge clk) (d) |-> (r) ;endproperty
assert property (SyncReseteotid_4);

property SyncReseteotid_5; @(posedge clk) (d) |-> (next_r) ;endproperty
assert property (SyncReseteotid_5);

property SyncReseteotid_6; @(posedge clk) (d) |-> (q) ;endproperty
assert property (SyncReseteotid_6);

property SyncReseteotid_7; @(posedge clk) (d) |-> (r) ;endproperty
assert property (SyncReseteotid_7);

property SyncReseteotid_8; @(posedge clk) (d) |-> (next_r) ;endproperty
assert property (SyncReseteotid_8);

property SyncReseteotid_9; @(posedge clk) (d) |-> (q) ;endproperty
assert property (SyncReseteotid_9);

property SyncReseteotid_10; @(posedge clk) (d) |-> (r) ;endproperty
assert property (SyncReseteotid_10);

property SyncReseteotid_11; @(posedge clk) (d) |-> (next_r) ;endproperty
assert property (SyncReseteotid_11);

property SyncReseteotid_12; @(posedge clk) (d) |-> (q) ;endproperty
assert property (SyncReseteotid_12);

property SyncReseteotid_13; @(posedge clk) (d) |-> (r) ;endproperty
assert property (SyncReseteotid_13);

property SyncReseteotid_14; @(posedge clk) (d) |-> (next_r) ;endproperty
assert property (SyncReseteotid_14);

property SyncReseteotid_15; @(posedge clk) (d) |-> (q) ;endproperty
assert property (SyncReseteotid_15);

property SyncReseteotid_16; @(posedge clk) (d) |-> (r) ;endproperty
assert property (SyncReseteotid_16);

property SyncReseteotid_17; @(posedge clk) (d) |-> (next_r) ;endproperty
assert property (SyncReseteotid_17);

property SyncReseteotid_18; @(posedge clk) (d) |-> (q) ;endproperty
assert property (SyncReseteotid_18);

property SyncReseteotid_19; @(posedge clk) (d) |-> (r) ;endproperty
assert property (SyncReseteotid_19);

property SyncReseteotid_20; @(posedge clk) (d) |-> (next_r) ;endproperty
assert property (SyncReseteotid_20);

property SyncReseteotid_21; @(posedge clk) (d) |-> (q) ;endproperty
assert property (SyncReseteotid_21);

property SyncReseteotid_22; @(posedge clk) (d) |-> (r) ;endproperty
assert property (SyncReseteotid_22);

property SyncReseteotid_23; @(posedge clk) (d) |-> (next_r) ;endproperty
assert property (SyncReseteotid_23);

property SyncReseteotid_24; @(posedge clk) (d) |-> (q) ;endproperty
assert property (SyncReseteotid_24);

property SyncReseteotid_25; @(posedge clk) (d) |-> (r) ;endproperty
assert property (SyncReseteotid_25);

property SyncReseteotid_26; @(posedge clk) (d) |-> (next_r) ;endproperty
assert property (SyncReseteotid_26);

property SyncReseteotid_27; @(posedge clk) (d) |-> (q) ;endproperty
assert property (SyncReseteotid_27);

property SyncReseteotid_28; @(posedge clk) (d) |-> (r) ;endproperty
assert property (SyncReseteotid_28);

property SyncReseteotid_29; @(posedge clk) (d) |-> (next_r) ;endproperty
assert property (SyncReseteotid_29);

property SyncReseteotid_30; @(posedge clk) (d) |-> (q) ;endproperty
assert property (SyncReseteotid_30);

property SyncReseteotid_31; @(posedge clk) (d) |-> (r) ;endproperty
assert property (SyncReseteotid_31);

property SyncReseteotid_32; @(posedge clk) (d) |-> (next_r) ;endproperty
assert property (SyncReseteotid_32);

property SyncReseteotid_33; @(posedge clk) (d) |-> (q) ;endproperty
assert property (SyncReseteotid_33);

property SyncReseteotid_34; @(posedge clk) (d) |-> (r) ;endproperty
assert property (SyncReseteotid_34);

property SyncReseteotid_35; @(posedge clk) (d) |-> (next_r) ;endproperty
assert property (SyncReseteotid_35);

property SyncReseteotid_36; @(posedge clk) (d) |-> (q) ;endproperty
assert property (SyncReseteotid_36);

property SyncReseteotid_37; @(posedge clk) (d) |-> (r) ;endproperty
assert property (SyncReseteotid_37);

property SyncReseteotid_38; @(posedge clk) (d) |-> (next_r) ;endproperty
assert property (SyncReseteotid_38);

property SyncReseteotid_39; @(posedge clk) (d) |-> (q) ;endproperty
assert property (SyncReseteotid_39);

property SyncReseteotid_40; @(posedge clk) (d) |-> (r) ;endproperty
assert property (SyncReseteotid_40);

property SyncReseteotid_41; @(posedge clk) (d) |-> (next_r) ;endproperty
assert property (SyncReseteotid_41);

property SyncReseteotid_42; @(posedge clk) (d) |-> (q) ;endproperty
assert property (SyncReseteotid_42);

property SyncReseteotid_43; @(posedge clk) (d) |-> (r) ;endproperty
assert property (SyncReseteotid_43);

property SyncReseteotid_44; @(posedge clk) (d) |-> (next_r) ;endproperty
assert property (SyncReseteotid_44);

property SyncReseteotid_45; @(posedge clk) (d) |-> (q) ;endproperty
assert property (SyncReseteotid_45);

property SyncReseteotid_46; @(posedge clk) (d) |-> (r) ;endproperty
assert property (SyncReseteotid_46);

property SyncReseteotid_47; @(posedge clk) (d) |-> (next_r) ;endproperty
assert property (SyncReseteotid_47);

property SyncReseteotid_48; @(posedge clk) (d) |-> (q) ;endproperty
assert property (SyncReseteotid_48);

property SyncReseteotid_49; @(posedge clk) (d) |-> (r) ;endproperty
assert property (SyncReseteotid_49);

property SyncReseteotid_50; @(posedge clk) (d) |-> (next_r) ;endproperty
assert property (SyncReseteotid_50);

property SyncReseteotid_51; @(posedge clk) (d) |-> (q) ;endproperty
assert property (SyncReseteotid_51);

property SyncReseteotid_52; @(posedge clk) (d) |-> (r) ;endproperty
assert property (SyncReseteotid_52);

property SyncReseteotid_53; @(posedge clk) (d) |-> (next_r) ;endproperty
assert property (SyncReseteotid_53);

property SyncReseteotid_54; @(posedge clk) (d) |-> (q) ;endproperty
assert property (SyncReseteotid_54);

property SyncReseteotid_55; @(posedge clk) (d) |-> (r) ;endproperty
assert property (SyncReseteotid_55);

property SyncReseteotid_56; @(posedge clk) (d) |-> (next_r) ;endproperty
assert property (SyncReseteotid_56);

property SyncReseteotid_57; @(posedge clk) (d) |-> (q) ;endproperty
assert property (SyncReseteotid_57);

property SyncReseteotid_58; @(posedge clk) (d) |-> (r) ;endproperty
assert property (SyncReseteotid_58);

property SyncReseteotid_59; @(posedge clk) (d) |-> (next_r) ;endproperty
assert property (SyncReseteotid_59);

property SyncReseteotid_60; @(posedge clk) (d) |-> (q) ;endproperty
assert property (SyncReseteotid_60);

property SyncReseteotid_61; @(posedge clk) (d) |-> (r) ;endproperty
assert property (SyncReseteotid_61);

property SyncReseteotid_62; @(posedge clk) (d) |-> (next_r) ;endproperty
assert property (SyncReseteotid_62);

property SyncReseteotid_63; @(posedge clk) (d) |-> (q) ;endproperty
assert property (SyncReseteotid_63);

property SyncReseteotid_64; @(posedge clk) (d) |-> (r) ;endproperty
assert property (SyncReseteotid_64);

property SyncReseteotid_65; @(posedge clk) (d) |-> (next_r) ;endproperty
assert property (SyncReseteotid_65);

property SyncReseteotid_66; @(posedge clk) (d) |-> (q) ;endproperty
assert property (SyncReseteotid_66);

property SyncReseteotid_67; @(posedge clk) (d) |-> (r) ;endproperty
assert property (SyncReseteotid_67);

property SyncReseteotid_68; @(posedge clk) (d) |-> (next_r) ;endproperty
assert property (SyncReseteotid_68);

property SyncReseteotid_69; @(posedge clk) (d) |-> (q) ;endproperty
assert property (SyncReseteotid_69);

property SyncReseteotid_70; @(posedge clk) (d) |-> (r) ;endproperty
assert property (SyncReseteotid_70);

property SyncReseteotid_71; @(posedge clk) (d) |-> (next_r) ;endproperty
assert property (SyncReseteotid_71);

property SyncReseteotid_72; @(posedge clk) (d) |-> (q) ;endproperty
assert property (SyncReseteotid_72);

property SyncReseteotid_73; @(posedge clk) (d) |-> (r) ;endproperty
assert property (SyncReseteotid_73);

property SyncReseteotid_74; @(posedge clk) (d) |-> (next_r) ;endproperty
assert property (SyncReseteotid_74);

property SyncReseteotid_75; @(posedge clk) (d) |-> (q) ;endproperty
assert property (SyncReseteotid_75);

property SyncReseteotid_76; @(posedge clk) (d) |-> (r) ;endproperty
assert property (SyncReseteotid_76);

property SyncReseteotid_77; @(posedge clk) (d) |-> (next_r) ;endproperty
assert property (SyncReseteotid_77);

property SyncReseteotid_78; @(posedge clk) (d) |-> (q) ;endproperty
assert property (SyncReseteotid_78);

property SyncReseteotid_79; @(posedge clk) (d) |-> (r) ;endproperty
assert property (SyncReseteotid_79);

property SyncReseteotid_80; @(posedge clk) (d) |-> (next_r) ;endproperty
assert property (SyncReseteotid_80);

property SyncReseteotid_81; @(posedge clk) (d) |-> (q) ;endproperty
assert property (SyncReseteotid_81);

property SyncReseteotid_82; @(posedge clk) (d) |-> (r) ;endproperty
assert property (SyncReseteotid_82);

property SyncReseteotid_83; @(posedge clk) (d) |-> (next_r) ;endproperty
assert property (SyncReseteotid_83);

endmodule