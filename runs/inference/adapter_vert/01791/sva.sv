property ClockSynceotid; @(posedge clk_in_1) (and0_out) == (in1) && (in2) ; endproperty 
 
 property ValidSynceotid; @(posedge clk_in_1) (and1_out) == (in3) && (in4) ; endproperty 
 
 property ValidSynceotid; @(posedge clk_in_1) (and2_out) == (in5) && (in6) ; endproperty 
 
 property ValidSynceotid; @(posedge clk_in_1) (and3_out) == (in7) && (in8) ; endproperty 
 
 property ValidSynceotid; @(posedge clk_in_1) (and4_out) == (and0_out) && (and1_out) ; endproperty 
 
 property ValidSynceotid; @(posedge clk_in_1) (and5_out) == (and2_out) && (and3_out) ; endproperty 
 
 property ValidSynceotid; @(posedge clk_in_1) (and6_out) == (and4_out) && (and5_out) ; endproperty 
 
 property ValidSynceotid; @(posedge clk_in_1) (and7_out) == (and6_out) && (in9) ; endproperty 
 
 property ValidOuteotid; @(posedge clk_in_1) (out1) == (and7_out) ; endproperty 
 