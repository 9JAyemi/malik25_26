property ORSynceotid; @(posedge clk_osc_16) (A) |-> (X) ;endproperty 
 
 property ORSynceotid; @(posedge clk_osc_16) (B) |-> (X) ;endproperty 
 
 property ORSynceotid; @(posedge clk_osc_16) (C) |-> (X) ;endproperty 
 
 property ORSynceotid; @(posedge clk_osc_16) (A) && @(posedge clk_osc_16) (B) && @(posedge clk_osc_16) (C) |-> (X) ;endproperty 
 