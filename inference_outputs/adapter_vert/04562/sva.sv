property ClockSynceotid; @(posedge clk_in_1) (sel1) && (sel0) |-> (out) == (in3) ; endproperty 
 
 property ValidSleotid; @(posedge clk_in_1) (sel1) && (!sel0) |-> (out) == (in2) ; endproperty 
 
 property ValidSleotid; @(posedge clk_in_1) (!sel1) && (sel0) |-> (out) == (in1) ; endproperty 
 
 property ValidSleotid; @(posedge clk_in_1) (!sel1) && (!sel0) |-> (out) == (in0) ; endproperty 
 