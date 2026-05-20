module reverse_last_two_bits_sva (
    input logic clk,
    input logic in,
    input logic out,
    input logic b0000,
    input logic b0001,
    input logic b0010,
    input logic b0011,
    input logic b0100,
    input logic b0101,
    input logic b0110,
    input logic b0111,
    input logic b1000,
    input logic b1001,
    input logic b1010,
    input logic b1011,
    input logic b1100,
    input logic b1101,
    input logic b1110,
    input logic b1111
);

property ClockSynceotid; @(posedge clk) (in) |-> (out) == {in[1:0], in[3:2]}; endproperty
assert property (ClockSynceotid);

property SyncIneotid; @(posedge clk) (in) |-> (out) != 4'b0000 ; endproperty
assert property (SyncIneotid);

property SyncIneotid_2; @(posedge clk) (in) |-> (out) != 4'b1111 ; endproperty
assert property (SyncIneotid_2);

property SyncIneotid_3; @(posedge clk) (in) |-> (out) != 4'b1100 ; endproperty
assert property (SyncIneotid_3);

property SyncIneotid_4; @(posedge clk) (in) |-> (out) != 4'b0011 ; endproperty
assert property (SyncIneotid_4);

property SyncIneotid_5; @(posedge clk) (in) |-> (out) != 4'b1010 ; endproperty
assert property (SyncIneotid_5);

property SyncIneotid_6; @(posedge clk) (in) |-> (out) != 4'b0101 ; endproperty
assert property (SyncIneotid_6);

property SyncIneotid_7; @(posedge clk) (in) |-> (out) != 4'b1001 ; endproperty
assert property (SyncIneotid_7);

property SyncIneotid_8; @(posedge clk) (in) |-> (out) != 4'b0110 ; endproperty
assert property (SyncIneotid_8);

property SyncIneotid_9; @(posedge clk) (in) |-> (out) != 4'b1101 ; endproperty
assert property (SyncIneotid_9);

property SyncIneotid_10; @(posedge clk) (in) |-> (out) != 4'b0010 ; endproperty
assert property (SyncIneotid_10);

property SyncIneotid_11; @(posedge clk) (in) |-> (out) != 4'b1011 ; endproperty
assert property (SyncIneotid_11);

property SyncIneotid_12; @(posedge clk) (in) |-> (out) != 4'b0111 ; endproperty
assert property (SyncIneotid_12);

property SyncIneotid_13; @(posedge clk) (in) |-> (out) != 4'b1110 ; endproperty
assert property (SyncIneotid_13);

property SyncIneotid_14; @(posedge clk) (in) |-> (out) != 4'b0001 ; endproperty
assert property (SyncIneotid_14);

property SyncIneotid_15; @(posedge clk) (in) |-> (out) != 4'b1000 ; endproperty
assert property (SyncIneotid_15);

property SyncIneotid_16; @(posedge clk) (in) |-> (out) != 4'b0100 ; endproperty
assert property (SyncIneotid_16);

property SyncIneotid_17; @(posedge clk) (in) |-> (out) != 4'b1100 ; endproperty
assert property (SyncIneotid_17);

property SyncIneotid_18; @(posedge clk) (in) |-> (out) != 4'b0011 ; endproperty
assert property (SyncIneotid_18);

property SyncIneotid_19; @(posedge clk) (in) |-> (out) != 4'b1010 ; endproperty
assert property (SyncIneotid_19);

property SyncIneotid_20; @(posedge clk) (in) |-> (out) != 4'b0101 ; endproperty
assert property (SyncIneotid_20);

property SyncIneotid_21; @(posedge clk) (in) |-> (out) != 4'b1001 ; endproperty
assert property (SyncIneotid_21);

property SyncIneotid_22; @(posedge clk) (in) |-> (out) != 4'b0110 ; endproperty
assert property (SyncIneotid_22);

property SyncIneotid_23; @(posedge clk) (in) |-> (out) != 4'b1101 ; endproperty
assert property (SyncIneotid_23);

property SyncIneotid_24; @(posedge clk) (in) |-> (out) != 4'b0010 ; endproperty
assert property (SyncIneotid_24);

property SyncIneotid_25; @(posedge clk) (in) |-> (out) != 4'b1011 ; endproperty
assert property (SyncIneotid_25);

property SyncIneotid_26; @(posedge clk) (in) |-> (out) != 4'b0111 ; endproperty
assert property (SyncIneotid_26);

property SyncIneotid_27; @(posedge clk) (in) |-> (out) != 4'b1110 ; endproperty
assert property (SyncIneotid_27);

property SyncIneotid_28; @(posedge clk) (in) |-> (out) != 4'b0001 ; endproperty
assert property (SyncIneotid_28);

property SyncIneotid_29; @(posedge clk) (in) |-> (out) != 4'b1000 ; endproperty
assert property (SyncIneotid_29);

property SyncIneotid_30; @(posedge clk) (in) |-> (out) != 4'b0100 ; endproperty
assert property (SyncIneotid_30);

property SyncIneotid_31; @(posedge clk) (in) |-> (out) != 4'b1100 ; endproperty
assert property (SyncIneotid_31);

property SyncIneotid_32; @(posedge clk) (in) |-> (out) != 4'b0011 ; endproperty
assert property (SyncIneotid_32);

property SyncIneotid_33; @(posedge clk) (in) |-> (out) != 4'b1010 ; endproperty
assert property (SyncIneotid_33);

property SyncIneotid_34; @(posedge clk) (in) |-> (out) != 4'b0101 ; endproperty
assert property (SyncIneotid_34);

property SyncIneotid_35; @(posedge clk) (in) |-> (out) != 4'b1001 ; endproperty
assert property (SyncIneotid_35);

property SyncIneotid_36; @(posedge clk) (in) |-> (out) != 4'b0110 ; endproperty
assert property (SyncIneotid_36);

property SyncIneotid_37; @(posedge clk) (in) |-> (out) != 4'b1101 ; endproperty
assert property (SyncIneotid_37);

property SyncIneotid_38; @(posedge clk) (in) |-> (out) != 4'b0010 ; endproperty
assert property (SyncIneotid_38);

property SyncIneotid_39; @(posedge clk) (in) |-> (out) != 4'b1011 ; endproperty
assert property (SyncIneotid_39);

property SyncIneotid_40; @(posedge clk) (in) |-> (out) != 4'b0111 ; endproperty
assert property (SyncIneotid_40);

property SyncIneotid_41; @(posedge clk) (in) |-> (out) != 4'b1110 ; endproperty
assert property (SyncIneotid_41);

property SyncIneotid_42; @(posedge clk) (in) |-> (out) != 4'b0001 ; endproperty
assert property (SyncIneotid_42);

property SyncIneotid_43; @(posedge clk) (in) |-> (out) != 4'b1000 ; endproperty
assert property (SyncIneotid_43);

property SyncIneotid_44; @(posedge clk) (in) |-> (out) != 4'b0100 ; endproperty
assert property (SyncIneotid_44);

property SyncIneotid_45; @(posedge clk) (in) |-> (out) != 4'b1100 ; endproperty
assert property (SyncIneotid_45);

property SyncIneotid_46; @(posedge clk) (in) |-> (out) != 4'b0011 ; endproperty
assert property (SyncIneotid_46);

property SyncIneotid_47; @(posedge clk) (in) |-> (out) != 4'b1010 ; endproperty
assert property (SyncIneotid_47);

property SyncIneotid_48; @(posedge clk) (in) |-> (out) != 4'b0101 ; endproperty
assert property (SyncIneotid_48);

property SyncIneotid_49; @(posedge clk) (in) |-> (out) != 4'b1001 ; endproperty
assert property (SyncIneotid_49);

property SyncIneotid_50; @(posedge clk) (in) |-> (out) != 4'b0110 ; endproperty
assert property (SyncIneotid_50);

property SyncIneotid_51; @(posedge clk) (in) |-> (out) != 4'b1101 ; endproperty
assert property (SyncIneotid_51);

property SyncIneotid_52; @(posedge clk) (in) |-> (out) != 4'b0010 ; endproperty
assert property (SyncIneotid_52);

property SyncIneotid_53; @(posedge clk) (in) |-> (out) != 4'b1011 ; endproperty
assert property (SyncIneotid_53);

property SyncIneotid_54; @(posedge clk) (in) |-> (out) != 4'b0111 ; endproperty
assert property (SyncIneotid_54);

property SyncIneotid_55; @(posedge clk) (in) |-> (out) != 4'b1110 ; endproperty
assert property (SyncIneotid_55);

property SyncIneotid_56; @(posedge clk) (in) |-> (out) != 4'b0001 ; endproperty
assert property (SyncIneotid_56);

property SyncIneotid_57; @(posedge clk) (in) |-> (out) != 4'b1000 ; endproperty
assert property (SyncIneotid_57);

property SyncIneotid_58; @(posedge clk) (in) |-> (out) != 4'b0100 ; endproperty
assert property (SyncIneotid_58);

property SyncIneotid_59; @(posedge clk) (in) |-> (out) != 4'b1100 ; endproperty
assert property (SyncIneotid_59);

property SyncIneotid_60; @(posedge clk) (in) |-> (out) != 4'b0011 ; endproperty
assert property (SyncIneotid_60);

property SyncIneotid_61; @(posedge clk) (in) |-> (out) != 4'b1010 ; endproperty
assert property (SyncIneotid_61);

property SyncIneotid_62; @(posedge clk) (in) |-> (out) != 4'b0101 ; endproperty
assert property (SyncIneotid_62);

endmodule