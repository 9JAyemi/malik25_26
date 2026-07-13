property ValidOnRiseeotid; @(posedge clk_in_1) (A) && (B) && (C) |-> (Y) ;endproperty 
 
 property ValidOnRiseeotid; @(posedge clk_in_1) (A) && (B) && (!C) |-> !(Y) ;endproperty 
 
 property ValidOnRiseeotid; @(posedge clk_in_1) (A) && (!B) && (C) |-> !(Y) ;endproperty 
 
 property ValidOnRiseeotid; @(posedge clk_in_1) (A) && (!B) && (!C) |-> !(Y) ;endproperty 
 
 property ValidOnRiseeotid; @(posedge clk_in_1) (!A) && (B) && (C) |-> !(Y) ;endproperty 
 
 property ValidOnRiseeotid; @(posedge clk_in_1) (!A) && (B) && (!C) |-> !(Y) ;endproperty 
 
 property ValidOnRiseeotid; @(posedge clk_in_1) (!A) && (!B) && (C) |-> !(Y) ;endproperty 
 
 property ValidOnRiseeotid; @(posedge clk_in_1) (!A) && (!B) && (!C) |-> !(Y) ;endproperty 
 