module top_module_sva (
    input logic clk,
    input logic converter_out,
    input logic counter_out,
    input logic functional_out,
    input logic reset,
    input logic signed_mag,
    input logic b0
);

property ResetSynceotid; @(posedge clk) (reset) |-> (functional_out == 8'b0) ;endproperty
assert property (ResetSynceotid);

property ResetSynceotid_2; @(posedge clk) (reset) |-> (counter_out == 4'b0) ;endproperty
assert property (ResetSynceotid_2);

property ResetSynceotid_3; @(posedge clk) (reset) |-> (converter_out == signed_mag) ;endproperty
assert property (ResetSynceotid_3);

property ResetSynceotid_4; @(posedge clk) (reset) |-> (functional_out == 8'b0) ;endproperty
assert property (ResetSynceotid_4);

property ResetSynceotid_5; @(posedge clk) (reset) |-> (counter_out == 4'b0) ;endproperty
assert property (ResetSynceotid_5);

property ResetSynceotid_6; @(posedge clk) (reset) |-> (converter_out == signed_mag) ;endproperty
assert property (ResetSynceotid_6);

property ResetSynceotid_7; @(posedge clk) (reset) |-> (functional_out == 8'b0) ;endproperty
assert property (ResetSynceotid_7);

property ResetSynceotid_8; @(posedge clk) (reset) |-> (counter_out == 4'b0) ;endproperty
assert property (ResetSynceotid_8);

property ResetSynceotid_9; @(posedge clk) (reset) |-> (converter_out == signed_mag) ;endproperty
assert property (ResetSynceotid_9);

property ResetSynceotid_10; @(posedge clk) (reset) |-> (functional_out == 8'b0) ;endproperty
assert property (ResetSynceotid_10);

property ResetSynceotid_11; @(posedge clk) (reset) |-> (counter_out == 4'b0) ;endproperty
assert property (ResetSynceotid_11);

property ResetSynceotid_12; @(posedge clk) (reset) |-> (converter_out == signed_mag) ;endproperty
assert property (ResetSynceotid_12);

property ResetSynceotid_13; @(posedge clk) (reset) |-> (functional_out == 8'b0) ;endproperty
assert property (ResetSynceotid_13);

property ResetSynceotid_14; @(posedge clk) (reset) |-> (counter_out == 4'b0) ;endproperty
assert property (ResetSynceotid_14);

property ResetSynceotid_15; @(posedge clk) (reset) |-> (converter_out == signed_mag) ;endproperty
assert property (ResetSynceotid_15);

property ResetSynceotid_16; @(posedge clk) (reset) |-> (functional_out == 8'b0) ;endproperty
assert property (ResetSynceotid_16);

property ResetSynceotid_17; @(posedge clk) (reset) |-> (counter_out == 4'b0) ;endproperty
assert property (ResetSynceotid_17);

property ResetSynceotid_18; @(posedge clk) (reset) |-> (converter_out == signed_mag) ;endproperty
assert property (ResetSynceotid_18);

property ResetSynceotid_19; @(posedge clk) (reset) |-> (functional_out == 8'b0) ;endproperty
assert property (ResetSynceotid_19);

property ResetSynceotid_20; @(posedge clk) (reset) |-> (counter_out == 4'b0) ;endproperty
assert property (ResetSynceotid_20);

property ResetSynceotid_21; @(posedge clk) (reset) |-> (converter_out == signed_mag) ;endproperty
assert property (ResetSynceotid_21);

property ResetSynceotid_22; @(posedge clk) (reset) |-> (functional_out == 8'b0) ;endproperty
assert property (ResetSynceotid_22);

property ResetSynceotid_23; @(posedge clk) (reset) |-> (counter_out == 4'b0) ;endproperty
assert property (ResetSynceotid_23);

property ResetSynceotid_24; @(posedge clk) (reset) |-> (converter_out == signed_mag) ;endproperty
assert property (ResetSynceotid_24);

property ResetSynceotid_25; @(posedge clk) (reset) |-> (functional_out == 8'b0) ;endproperty
assert property (ResetSynceotid_25);

property ResetSynceotid_26; @(posedge clk) (reset) |-> (counter_out == 4'b0) ;endproperty
assert property (ResetSynceotid_26);

property ResetSynceotid_27; @(posedge clk) (reset) |-> (converter_out == signed_mag) ;endproperty
assert property (ResetSynceotid_27);

property ResetSynceotid_28; @(posedge clk) (reset) |-> (functional_out == 8'b0) ;endproperty
assert property (ResetSynceotid_28);

property ResetSynceotid_29; @(posedge clk) (reset) |-> (counter_out == 4'b0) ;endproperty
assert property (ResetSynceotid_29);

property ResetSynceotid_30; @(posedge clk) (reset) |-> (converter_out == signed_mag) ;endproperty
assert property (ResetSynceotid_30);

property ResetSynceotid_31; @(posedge clk) (reset) |-> (functional_out == 8'b0) ;endproperty
assert property (ResetSynceotid_31);

property ResetSynceotid_32; @(posedge clk) (reset) |-> (counter_out == 4'b0) ;endproperty
assert property (ResetSynceotid_32);

property ResetSynceotid_33; @(posedge clk) (reset) |-> (converter_out == signed_mag) ;endproperty
assert property (ResetSynceotid_33);

property ResetSynceotid_34; @(posedge clk) (reset) |-> (functional_out == 8'b0) ;endproperty
assert property (ResetSynceotid_34);

property ResetSynceotid_35; @(posedge clk) (reset) |-> (counter_out == 4'b0) ;endproperty
assert property (ResetSynceotid_35);

property ResetSynceotid_36; @(posedge clk) (reset) |-> (converter_out == signed_mag) ;endproperty
assert property (ResetSynceotid_36);

property ResetSynceotid_37; @(posedge clk) (reset) |-> (functional_out == 8'b0) ;endproperty
assert property (ResetSynceotid_37);

property ResetSynceotid_38; @(posedge clk) (reset) |-> (counter_out == 4'b0) ;endproperty
assert property (ResetSynceotid_38);

property ResetSynceotid_39; @(posedge clk) (reset) |-> (converter_out == signed_mag) ;endproperty
assert property (ResetSynceotid_39);

property ResetSynceotid_40; @(posedge clk) (reset) |-> (functional_out == 8'b0) ;endproperty
assert property (ResetSynceotid_40);

property ResetSynceotid_41; @(posedge clk) (reset) |-> (counter_out == 4'b0) ;endproperty
assert property (ResetSynceotid_41);

property ResetSynceotid_42; @(posedge clk) (reset) |-> (converter_out == signed_mag) ;endproperty
assert property (ResetSynceotid_42);

property ResetSynceotid_43; @(posedge clk) (reset) |-> (functional_out == 8'b0) ;endproperty
assert property (ResetSynceotid_43);

property ResetSynceotid_44; @(posedge clk) (reset) |-> (counter_out == 4'b0) ;endproperty
assert property (ResetSynceotid_44);

property ResetSynceotid_45; @(posedge clk) (reset) |-> (converter_out == signed_mag) ;endproperty
assert property (ResetSynceotid_45);

property ResetSynceotid_46; @(posedge clk) (reset) |-> (functional_out == 8'b0) ;endproperty
assert property (ResetSynceotid_46);

property ResetSynceotid_47; @(posedge clk) (reset) |-> (counter_out == 4'b0) ;endproperty
assert property (ResetSynceotid_47);

property ResetSynceotid_48; @(posedge clk) (reset) |-> (converter_out == signed_mag) ;endproperty
assert property (ResetSynceotid_48);

property ResetSynceotid_49; @(posedge clk) (reset) |-> (functional_out == 8'b0) ;endproperty
assert property (ResetSynceotid_49);

property ResetSynceotid_50; @(posedge clk) (reset) |-> (counter_out == 4'b0) ;endproperty
assert property (ResetSynceotid_50);

property ResetSynceotid_51; @(posedge clk) (reset) |-> (converter_out == signed_mag) ;endproperty
assert property (ResetSynceotid_51);

property ResetSynceotid_52; @(posedge clk) (reset) |-> (functional_out == 8'b0) ;endproperty
assert property (ResetSynceotid_52);

property ResetSynceotid_53; @(posedge clk) (reset) |-> (counter_out == 4'b0) ;endproperty
assert property (ResetSynceotid_53);

property ResetSynceotid_54; @(posedge clk) (reset) |-> (converter_out == signed_mag) ;endproperty
assert property (ResetSynceotid_54);

property ResetSynceotid_55; @(posedge clk) (reset) |-> (functional_out == 8'b0) ;endproperty
assert property (ResetSynceotid_55);

property ResetSynceotid_56; @(posedge clk) (reset) |-> (counter_out == 4'b0) ;endproperty
assert property (ResetSynceotid_56);

property ResetSynceotid_57; @(posedge clk) (reset) |-> (converter_out == signed_mag) ;endproperty
assert property (ResetSynceotid_57);

property ResetSynceotid_58; @(posedge clk) (reset) |-> (functional_out == 8'b0) ;endproperty
assert property (ResetSynceotid_58);

property ResetSynceotid_59; @(posedge clk) (reset) |-> (counter_out == 4'b0) ;endproperty
assert property (ResetSynceotid_59);

property ResetSynceotid_60; @(posedge clk) (reset) |-> (converter_out == signed_mag) ;endproperty
assert property (ResetSynceotid_60);

property ResetSynceotid_61; @(posedge clk) (reset) |-> (functional_out == 8'b0) ;endproperty
assert property (ResetSynceotid_61);

property ResetSynceotid_62; @(posedge clk) (reset) |-> (counter_out == 4'b0) ;endproperty
assert property (ResetSynceotid_62);

property ResetSynceotid_63; @(posedge clk) (reset) |-> (converter_out == signed_mag) ;endproperty
assert property (ResetSynceotid_63);

property ResetSynceotid_64; @(posedge clk) (reset) |-> (functional_out == 8'b0) ;endproperty
assert property (ResetSynceotid_64);

property ResetSynceotid_65; @(posedge clk) (reset) |-> (counter_out == 4'b0) ;endproperty
assert property (ResetSynceotid_65);

property ResetSynceotid_66; @(posedge clk) (reset) |-> (converter_out == signed_mag) ;endproperty
assert property (ResetSynceotid_66);

property ResetSynceotid_67; @(posedge clk) (reset) |-> (functional_out == 8'b0) ;endproperty
assert property (ResetSynceotid_67);

property ResetSynceotid_68; @(posedge clk) (reset) |-> (counter_out == 4'b0) ;endproperty
assert property (ResetSynceotid_68);

property ResetSynceotid_69; @(posedge clk) (reset) |-> (converter_out == signed_mag) ;endproperty
assert property (ResetSynceotid_69);

endmodule