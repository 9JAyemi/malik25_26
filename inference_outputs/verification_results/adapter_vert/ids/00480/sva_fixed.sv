module adc_transformer_sva (
    input logic adc_clk,
    input logic adc_dat_a,
    input logic adc_dat_a_i,
    input logic adc_dat_a_o,
    input logic adc_dat_b,
    input logic adc_dat_b_i,
    input logic adc_dat_b_o
);

property ClockSynceotid; @(posedge adc_clk) (adc_dat_a_i) |-> adc_dat_a == adc_dat_a_i ;endproperty
assert property (ClockSynceotid);

property ClockSynceotid_2; @(posedge adc_clk) (adc_dat_b_i) |-> adc_dat_b == adc_dat_b_i ;endproperty
assert property (ClockSynceotid_2);

property ClockSynceotid_3; @(posedge adc_clk) (adc_dat_a_i) |-> adc_dat_a_o == {adc_dat_a[14-1], ~adc_dat_a[14-2:0]} ;endproperty
assert property (ClockSynceotid_3);

property ClockSynceotid_4; @(posedge adc_clk) (adc_dat_b_i) |-> adc_dat_b_o == {adc_dat_b[14-1], ~adc_dat_b[14-2:0]} ;endproperty
assert property (ClockSynceotid_4);

endmodule