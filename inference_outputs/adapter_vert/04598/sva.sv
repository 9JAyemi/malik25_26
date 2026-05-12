property AddOneeotid; @(posedge clk_in_1) (a) |-> (sum) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (b) |-> (sum) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (cin) |-> (sum) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (a) &&  (b) &&  (cin) |-> (cout) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (a) &&  (b) &&  (!cin) |-> !(cout) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (a) &&  (!b) &&  (cin) |-> !(cout) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (!a) &&  (b) &&  (cin) |-> !(cout) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (a) &&  (!b) &&  (!cin) |-> (cout) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (!a) &&  (b) &&  (!cin) |-> (cout) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (!a) &&  (!b) &&  (cin) |-> (cout) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1)  (a) &&  (b)  &&  (cin)  ||  (a) &&  (b)  &&  (!cin)  ||  (a) &&  (!b)  &&  (cin)  ||  (!a) &&  (b)  &&  (cin)  &&  (  !a  &&  !b  &&  !cin  ||  a  &&  b  &&  cin  ) ;endproperty 
 