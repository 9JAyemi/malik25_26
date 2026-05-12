property ClockSynceotid; @(posedge clk_in_15) (a) |-> (y) ;endproperty 
 
 property ValidSynceotid; @(posedge clk_in_15) (b) |-> (y) ;endproperty 
 
 property ValidSynceotid; @(posedge clk_in_15) (sel) |-> (a_and_sel) ;endproperty 
 
 property ValidSynceotid; @(posedge clk_in_15) (sel) |-> (b_and_not_sel) ;endproperty 
 
 property ValidSynceotid; @(posedge clk_in_15) (a) &&  (b) &&  (sel) |-> (y) ;endproperty 
 
 property ValidSynceotid; @(posedge clk_in_15) (a) &&  (b) &&  (!sel) |-> (y) ;endproperty 
 
 property ValidSynceotid; @(posedge clk_in_15) (b) &&  (!a) &&  (sel) |-> (y) ;endproperty 
 
 property ValidSynceotid; @(posedge clk_in_15) (a) &&  (!b) &&  (!sel) |-> (y) ;endproperty 
 