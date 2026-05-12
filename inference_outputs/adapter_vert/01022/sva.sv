property ORSynceotid; @(posedge clk_osc_19) (X) |-> (or0_out_X == B) && (or0_out_X == A) ;endproperty 
 
 property ORSynceotid; @(posedge clk_osc_19) (or0_out_X) == (B) &&  (A) |-> (X) == (or0_out_X) ;endproperty 
 