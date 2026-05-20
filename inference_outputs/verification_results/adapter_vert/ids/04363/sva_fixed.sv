module top_module_sva (
    input logic clk,
    input logic final_output,
    input logic reset,
    input logic b0,
    input logic counter_4bit,
    input logic ripple_carry_adder
);

property ResetSynceotid; @(posedge clk) (reset) |-> (counter_4bit) == (4'b0); endproperty
assert property (ResetSynceotid);

property ResetSynceotid_2; @(posedge clk) (reset) |-> (ripple_carry_adder) == (16'b0); endproperty
assert property (ResetSynceotid_2);

property ResetSynceotid_3; @(posedge clk) (reset) |-> (final_output) == (16'b0); endproperty
assert property (ResetSynceotid_3);

property ResetSynceotid_4; @(posedge clk) (reset) |-> (counter_4bit) == (4'b0) && (ripple_carry_adder) == (16'b0) && (final_output) == (16'b0); endproperty
assert property (ResetSynceotid_4);

property ResetSynceotid_5; @(posedge clk) (reset) |-> (counter_4bit) == (4'b0) && (ripple_carry_adder) == (16'b0) && (final_output) == (16'b0); endproperty
assert property (ResetSynceotid_5);

property ResetSynceotid_6; @(posedge clk) (reset) |-> (counter_4bit) == (4'b0) && (ripple_carry_adder) == (16'b0) && (final_output) == (16'b0); endproperty
assert property (ResetSynceotid_6);

property ResetSynceotid_7; @(posedge clk) (reset) |-> (counter_4bit) == (4'b0) && (ripple_carry_adder) == (16'b0) && (final_output) == (16'b0); endproperty
assert property (ResetSynceotid_7);

property ResetSynceotid_8; @(posedge clk) (reset) |-> (counter_4bit) == (4'b0) && (ripple_carry_adder) == (16'b0) && (final_output) == (16'b0); endproperty
assert property (ResetSynceotid_8);

property ResetSynceotid_9; @(posedge clk) (reset) |-> (counter_4bit) == (4'b0) && (ripple_carry_adder) == (16'b0) && (final_output) == (16'b0); endproperty
assert property (ResetSynceotid_9);

property ResetSynceotid_10; @(posedge clk) (reset) |-> (counter_4bit) == (4'b0) && (ripple_carry_adder) == (16'b0) && (final_output) == (16'b0); endproperty
assert property (ResetSynceotid_10);

property ResetSynceotid_11; @(posedge clk) (reset) |-> (counter_4bit) == (4'b0) && (ripple_carry_adder) == (16'b0) && (final_output) == (16'b0); endproperty
assert property (ResetSynceotid_11);

property ResetSynceotid_12; @(posedge clk) (reset) |-> (counter_4bit) == (4'b0) && (ripple_carry_adder) == (16'b0) && (final_output) == (16'b0); endproperty
assert property (ResetSynceotid_12);

property ResetSynceotid_13; @(posedge clk) (reset) |-> (counter_4bit) == (4'b0) && (ripple_carry_adder) == (16'b0) && (final_output) == (16'b0); endproperty
assert property (ResetSynceotid_13);

property ResetSynceotid_14; @(posedge clk) (reset) |-> (counter_4bit) == (4'b0) && (ripple_carry_adder) == (16'b0) && (final_output) == (16'b0); endproperty
assert property (ResetSynceotid_14);

property ResetSynceotid_15; @(posedge clk) (reset) |-> (counter_4bit) == (4'b0) && (ripple_carry_adder) == (16'b0) && (final_output) == (16'b0); endproperty
assert property (ResetSynceotid_15);

property ResetSynceotid_16; @(posedge clk) (reset) |-> (counter_4bit) == (4'b0) && (ripple_carry_adder) == (16'b0) && (final_output) == (16'b0); endproperty
assert property (ResetSynceotid_16);

property ResetSynceotid_17; @(posedge clk) (reset) |-> (counter_4bit) == (4'b0) && (ripple_carry_adder) == (16'b0) && (final_output) == (16'b0); endproperty
assert property (ResetSynceotid_17);

property ResetSynceotid_18; @(posedge clk) (reset) |-> (counter_4bit) == (4'b0) && (ripple_carry_adder) == (16'b0) && (final_output) == (16'b0); endproperty
assert property (ResetSynceotid_18);

property ResetSynceotid_19; @(posedge clk) (reset) |-> (counter_4bit) == (4'b0) && (ripple_carry_adder) == (16'b0) && (final_output) == (16'b0); endproperty
assert property (ResetSynceotid_19);

property ResetSynceotid_20; @(posedge clk) (reset) |-> (counter_4bit) == (4'b0) && (ripple_carry_adder) == (16'b0) && (final_output) == (16'b0); endproperty
assert property (ResetSynceotid_20);

property ResetSynceotid_21; @(posedge clk) (reset) |-> (counter_4bit) == (4'b0) && (ripple_carry_adder) == (16'b0) && (final_output) == (16'b0); endproperty
assert property (ResetSynceotid_21);

property ResetSynceotid_22; @(posedge clk) (reset) |-> (counter_4bit) == (4'b0) && (ripple_carry_adder) == (16'b0) && (final_output) == (16'b0); endproperty
assert property (ResetSynceotid_22);

property ResetSynceotid_23; @(posedge clk) (reset) |-> (counter_4bit) == (4'b0) && (ripple_carry_adder) == (16'b0) && (final_output) == (16'b0); endproperty
assert property (ResetSynceotid_23);

property ResetSynceotid_24; @(posedge clk) (reset) |-> (counter_4bit) == (4'b0) && (ripple_carry_adder) == (16'b0) && (final_output) == (16'b0); endproperty
assert property (ResetSynceotid_24);

property ResetSynceotid_25; @(posedge clk) (reset) |-> (counter_4bit) == (4'b0) && (ripple_carry_adder) == (16'b0) && (final_output) == (16'b0); endproperty
assert property (ResetSynceotid_25);

property ResetSynceotid_26; @(posedge clk) (reset) |-> (counter_4bit) == (4'b0) && (ripple_carry_adder) == (16'b0) && (final_output) == (16'b0); endproperty
assert property (ResetSynceotid_26);

property ResetSynceotid_27; @(posedge clk) (reset) |-> (counter_4bit) == (4'b0) && (ripple_carry_adder) == (16'b0) && (final_output) == (16'b0); endproperty
assert property (ResetSynceotid_27);

property ResetSynceotid_28; @(posedge clk) (reset) |-> (counter_4bit) == (4'b0) && (ripple_carry_adder) == (16'b0) && (final_output) == (16'b0); endproperty
assert property (ResetSynceotid_28);

property ResetSynceotid_29; @(posedge clk) (reset) |-> (counter_4bit) == (4'b0) && (ripple_carry_adder) == (16'b0) && (final_output) == (16'b0); endproperty
assert property (ResetSynceotid_29);

property ResetSynceotid_30; @(posedge clk) (reset) |-> (counter_4bit) == (4'b0) && (ripple_carry_adder) == (16'b0) && (final_output) == (16'b0); endproperty
assert property (ResetSynceotid_30);

property ResetSynceotid_31; @(posedge clk) (reset) |-> (counter_4bit) == (4'b0) && (ripple_carry_adder) == (16'b0) && (final_output) == (16'b0); endproperty
assert property (ResetSynceotid_31);

property ResetSynceotid_32; @(posedge clk) (reset) |-> (counter_4bit) == (4'b0) && (ripple_carry_adder) == (16'b0) && (final_output) == (16'b0); endproperty
assert property (ResetSynceotid_32);

property ResetSynceotid_33; @(posedge clk) (reset) |-> (counter_4bit) == (4'b0) && (ripple_carry_adder) == (16'b0) && (final_output) == (16'b0); endproperty
assert property (ResetSynceotid_33);

property ResetSynceotid_34; @(posedge clk) (reset) |-> (counter_4bit) == (4'b0) && (ripple_carry_adder) == (16'b0) && (final_output) == (16'b0); endproperty
assert property (ResetSynceotid_34);

property ResetSynceotid_35; @(posedge clk) (reset) |-> (counter_4bit) == (4'b0) && (ripple_carry_adder) == (16'b0) && (final_output) == (16'b0); endproperty
assert property (ResetSynceotid_35);

property ResetSynceotid_36; @(posedge clk) (reset) |-> (counter_4bit) == (4'b0) && (ripple_carry_adder) == (16'b0) && (final_output) == (16'b0); endproperty
assert property (ResetSynceotid_36);

endmodule