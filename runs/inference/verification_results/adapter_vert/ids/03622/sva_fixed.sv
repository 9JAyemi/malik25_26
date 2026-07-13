module key_expander_sva (
    input logic key_in,
    input logic cfg_11,
    input logic cfg_15,
    input logic cfg_19,
    input logic cfg_3,
    input logic cfg_7,
    input logic cfg_9,
    input logic clk_in_15,
    input logic core_18,
    input logic key_1,
    input logic key_10,
    input logic key_11,
    input logic key_12,
    input logic key_13,
    input logic key_14,
    input logic key_15,
    input logic key_2,
    input logic key_3,
    input logic key_4,
    input logic key_5,
    input logic key_6,
    input logic key_7,
    input logic key_8,
    input logic key_9,
    input logic reg_1,
    input logic reg_10,
    input logic reg_11,
    input logic reg_12,
    input logic reg_2,
    input logic reg_3,
    input logic reg_4,
    input logic reg_5,
    input logic reg_6,
    input logic reg_7,
    input logic reg_8,
    input logic reg_9
);

property ClockSynceotid; @(posedge clk_in_15) (key_in) |-> (key_15) ;endproperty
assert property (ClockSynceotid);

property KeySynceotid; @(posedge clk_in_15) (key_in) &&  (  reg_12  != core_18 ) |-> (key_14) ;endproperty
assert property (KeySynceotid);

property ValidSynceotid; @(posedge clk_in_15) (key_in) &&  (  reg_12  != core_18 ) &&  (  reg_11  != cfg_19 ) |-> (key_13) ;endproperty
assert property (ValidSynceotid);

property ValidSynceotid_2; @(posedge clk_in_15) (key_in) &&  (  reg_12  != core_18 ) &&  (  reg_11  != cfg_19 ) &&  (  reg_10  != cfg_15 ) |-> (key_12) ;endproperty
assert property (ValidSynceotid_2);

property ValidSynceotid_3; @(posedge clk_in_15) (key_in) &&  (  reg_12  != core_18 ) &&  (  reg_11  != cfg_19 ) &&  (  reg_10  != cfg_15 ) &&  (  reg_9  != cfg_11 ) |-> (key_11) ;endproperty
assert property (ValidSynceotid_3);

property ValidSynceotid_4; @(posedge clk_in_15) (key_in) &&  (  reg_12  != core_18 ) &&  (  reg_11  != cfg_19 ) &&  (  reg_10  != cfg_15 ) &&  (  reg_9  != cfg_11 ) &&  (  reg_8  != cfg_7 ) |-> (key_10) ;endproperty
assert property (ValidSynceotid_4);

property ValidSynceotid_5; @(posedge clk_in_15) (key_in) &&  (  reg_12  != core_18 ) &&  (  reg_11  != cfg_19 ) &&  (  reg_10  != cfg_15 ) &&  (  reg_9  != cfg_11 ) &&  (  reg_8  != cfg_7 ) &&  (  reg_7  != cfg_3 ) |-> (key_9) ;endproperty
assert property (ValidSynceotid_5);

property ValidSynceotid_6; @(posedge clk_in_15) (key_in) &&  (  reg_12  != core_18 ) &&  (  reg_11  != cfg_19 ) &&  (  reg_10  != cfg_15 ) &&  (  reg_9  != cfg_11 ) &&  (  reg_8  != cfg_7 ) &&  (  reg_7  != cfg_3 ) &&  (  reg_6  != cfg_19 ) |-> (key_8) ;endproperty
assert property (ValidSynceotid_6);

property ValidSynceotid_7; @(posedge clk_in_15) (key_in) &&  (  reg_12  != core_18 ) &&  (  reg_11  != cfg_19 ) &&  (  reg_10  != cfg_15 ) &&  (  reg_9  != cfg_11 ) &&  (  reg_8  != cfg_7 ) &&  (  reg_7  != cfg_3 ) &&  (  reg_6  != cfg_19 ) &&  (  reg_5  != cfg_15 ) |-> (key_7) ;endproperty
assert property (ValidSynceotid_7);

property ValidSynceotid_8; @(posedge clk_in_15) (key_in) &&  (  reg_12  != core_18 ) &&  (  reg_11  != cfg_19 ) &&  (  reg_10  != cfg_15 ) &&  (  reg_9  != cfg_11 ) &&  (  reg_8  != cfg_7 ) &&  (  reg_7  != cfg_3 ) &&  (  reg_6  != cfg_19 ) &&  (  reg_5  != cfg_15 ) &&  (  reg_4  != cfg_11 ) |-> (key_6) ;endproperty
assert property (ValidSynceotid_8);

property ValidSynceotid_9; @(posedge clk_in_15) (key_in) &&  (  reg_12  != core_18 ) &&  (  reg_11  != cfg_19 ) &&  (  reg_10  != cfg_15 ) &&  (  reg_9  != cfg_11 ) &&  (  reg_8  != cfg_7 ) &&  (  reg_7  != cfg_3 ) &&  (  reg_6  != cfg_19 ) &&  (  reg_5  != cfg_15 ) &&  (  reg_4  != cfg_11 ) &&  (  reg_3  != cfg_7 ) |-> (key_5) ;endproperty
assert property (ValidSynceotid_9);

property ValidSynceotid_10; @(posedge clk_in_15) (key_in) &&  (  reg_12  != core_18 ) &&  (  reg_11  != cfg_19 ) &&  (  reg_10  != cfg_15 ) &&  (  reg_9  != cfg_11 ) &&  (  reg_8  != cfg_7 ) &&  (  reg_7  != cfg_3 ) &&  (  reg_6  != cfg_19 ) &&  (  reg_5  != cfg_15 ) &&  (  reg_4  != cfg_11 ) &&  (  reg_3  != cfg_7 ) &&  (  reg_2  != cfg_3 ) |-> (key_4) ;endproperty
assert property (ValidSynceotid_10);

property ValidSynceotid_11; @(posedge clk_in_15) (key_in) &&  (  reg_12  != core_18 ) &&  (  reg_11  != cfg_19 ) &&  (  reg_10  != cfg_15 ) &&  (  reg_9  != cfg_11 ) &&  (  reg_8  != cfg_7 ) &&  (  reg_7  != cfg_3 ) &&  (  reg_6  != cfg_19 ) &&  (  reg_5  != cfg_15 ) &&  (  reg_4  != cfg_11 ) &&  (  reg_3  != cfg_7 ) &&  (  reg_2  != cfg_3 ) &&  (  reg_1  != cfg_9 ) |-> (key_3) ;endproperty
assert property (ValidSynceotid_11);

property ValidSynceotid_12; @(posedge clk_in_15) (key_in) &&  (  reg_12  != core_18 ) &&  (  reg_11  != cfg_19 ) &&  (  reg_10  != cfg_15 ) &&  (  reg_9  != cfg_11 ) &&  (  reg_8  != cfg_7 ) &&  (  reg_7  != cfg_3 ) &&  (  reg_6  != cfg_19 ) &&  (  reg_5  != cfg_15 ) &&  (  reg_4  != cfg_11 ) &&  (  reg_3  != cfg_7 ) &&  (  reg_2  != cfg_3 ) &&  (  reg_1  != cfg_9 ) &&  (  reg_10 ) |-> (key_2) ;endproperty
assert property (ValidSynceotid_12);

property ValidSynceotid_13; @(posedge clk_in_15) (key_in) &&  (  reg_12  != core_18 ) &&  (  reg_11  != cfg_19 ) &&  (  reg_10  != cfg_15 ) &&  (  reg_9  != cfg_11 ) &&  (  reg_8  != cfg_7 ) &&  (  reg_7  != cfg_3 ) &&  (  reg_6  != cfg_19 ) &&  (  reg_5  != cfg_15 ) &&  (  reg_4  != cfg_11 ) &&  (  reg_3  != cfg_7 ) &&  (  reg_2  != cfg_3 ) &&  (  reg_1  != cfg_9 ) &&  (  reg_10 ) &&  (  reg_9 ) |-> (key_1) ;endproperty
assert property (ValidSynceotid_13);

endmodule