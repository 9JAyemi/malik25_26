property ClockSynceotid; @(posedge adc_clk) (adc_dat_a_i) |-> adc_dat_a == adc_dat_a_i ;endproperty 
 
 property ClockSynceotid; @(posedge adc_clk) (adc_dat_b_i) |-> adc_dat_b == adc_dat_b_i ;endproperty 
 
 property ClockSynceotid; @(posedge adc_clk) (adc_dat_a_i) |-> adc_dat_a_o == {adc_dat_a[14-1], ~adc_dat_a[14-2:0]} ;endproperty 
 
 property ClockSynceotid; @(posedge adc_clk) (adc_dat_b_i) |-> adc_dat_b_o == {adc_dat_b[14-1], ~adc_dat_b[14-2:0]} ;endproperty 
 