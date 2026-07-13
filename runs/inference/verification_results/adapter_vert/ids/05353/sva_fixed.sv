module reverse_bit_order_sva (
    input logic clk,
    input logic in,
    input logic reversed,
    input logic shift_reg
);

property ClockSynceotid; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (ClockSynceotid);

property SyncRegeotid; @(posedge clk) (in) |-> (shift_reg) ;endproperty
assert property (SyncRegeotid);

property SyncRegeotid_2; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_2);

property SyncRegeotid_3; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_3);

property SyncRegeotid_4; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_4);

property SyncRegeotid_5; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_5);

property SyncRegeotid_6; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_6);

property SyncRegeotid_7; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_7);

property SyncRegeotid_8; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_8);

property SyncRegeotid_9; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_9);

property SyncRegeotid_10; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_10);

property SyncRegeotid_11; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_11);

property SyncRegeotid_12; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_12);

property SyncRegeotid_13; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_13);

property SyncRegeotid_14; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_14);

property SyncRegeotid_15; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_15);

property SyncRegeotid_16; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_16);

property SyncRegeotid_17; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_17);

property SyncRegeotid_18; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_18);

property SyncRegeotid_19; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_19);

property SyncRegeotid_20; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_20);

property SyncRegeotid_21; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_21);

property SyncRegeotid_22; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_22);

property SyncRegeotid_23; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_23);

property SyncRegeotid_24; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_24);

property SyncRegeotid_25; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_25);

property SyncRegeotid_26; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_26);

property SyncRegeotid_27; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_27);

property SyncRegeotid_28; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_28);

property SyncRegeotid_29; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_29);

property SyncRegeotid_30; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_30);

property SyncRegeotid_31; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_31);

property SyncRegeotid_32; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_32);

property SyncRegeotid_33; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_33);

property SyncRegeotid_34; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_34);

property SyncRegeotid_35; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_35);

property SyncRegeotid_36; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_36);

property SyncRegeotid_37; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_37);

property SyncRegeotid_38; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_38);

property SyncRegeotid_39; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_39);

property SyncRegeotid_40; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_40);

property SyncRegeotid_41; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_41);

property SyncRegeotid_42; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_42);

property SyncRegeotid_43; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_43);

property SyncRegeotid_44; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_44);

property SyncRegeotid_45; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_45);

property SyncRegeotid_46; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_46);

property SyncRegeotid_47; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_47);

property SyncRegeotid_48; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_48);

property SyncRegeotid_49; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_49);

property SyncRegeotid_50; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_50);

property SyncRegeotid_51; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_51);

property SyncRegeotid_52; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_52);

property SyncRegeotid_53; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_53);

property SyncRegeotid_54; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_54);

property SyncRegeotid_55; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_55);

property SyncRegeotid_56; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_56);

property SyncRegeotid_57; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_57);

property SyncRegeotid_58; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_58);

property SyncRegeotid_59; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_59);

property SyncRegeotid_60; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_60);

property SyncRegeotid_61; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_61);

property SyncRegeotid_62; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_62);

property SyncRegeotid_63; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_63);

property SyncRegeotid_64; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_64);

property SyncRegeotid_65; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_65);

property SyncRegeotid_66; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_66);

property SyncRegeotid_67; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_67);

property SyncRegeotid_68; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_68);

property SyncRegeotid_69; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_69);

property SyncRegeotid_70; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_70);

property SyncRegeotid_71; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_71);

property SyncRegeotid_72; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_72);

property SyncRegeotid_73; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_73);

property SyncRegeotid_74; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_74);

property SyncRegeotid_75; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_75);

property SyncRegeotid_76; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_76);

property SyncRegeotid_77; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_77);

property SyncRegeotid_78; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_78);

property SyncRegeotid_79; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_79);

property SyncRegeotid_80; @(posedge clk) (in) |-> (reversed) ;endproperty
assert property (SyncRegeotid_80);

endmodule