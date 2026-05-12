property AddOneeotid; @(posedge clk_in_1) (a) == (1'b0) && (b) == (1'b0) && (cin) == (1'b0) |-> (sum) == (1'b0); endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (a) == (1'b0) && (b) == (1'b0) && (cin) != (1'b0) |-> (sum) == (1'b1); endproperty 
 
 property CarryOn; @(posedge clk_in_1) (a) != (1'b0) && (b) != (1'b0) && (cin) != (1'b0) |-> (sum) == (1'b1); endproperty 
 
 property CarryOneeotid; @(posedge clk_in_1) (a) != (1'b0) && (b) == (1'b0) && (cin) == (1'b0) |-> (sum) == (1'b1); endproperty 
 
 property CarryOneeotid; @(posedge clk_in_1) (a) == (1'b0) && (b) != (1'b0) && (cin) == (1'b0) |-> (sum) == (1'b1); endproperty 
 
 property CarryOneeotid; @(posedge clk_in_1) (a) != (1'b0) && (b) != (1'b0) && (cin) == (1'b0) |-> (sum) == (1'b0); endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (a) != (1'b0) && (b) == (1'b0) && (cin) != (1'b0) |-> (sum) == (1'b0); endproperty 
 
 property CarryOneeotid; @(posedge clk_in_1) (a) == (1'b0) && (b) != (1'b0) && (cin) != (1'b0) |-> (sum) == (1'b0); endproperty 
 
 property CarryOneeotid; @(posedge clk_in_1) (a) != (1'b0) && (b) != (1'b0) && (cin) != (1'b0) |-> (sum) == (1'b1); endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (a) != (1'b0) && (b) != (1'b0) && (cin) != (1'b0) &&  (sum) != (1'b1)  |->  (cout) ; endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (a) != (1'b0) && (b) != (1'b0) && (cin) != (1'b0) &&  (sum)  == (1'b1)  |->  (cout) != 1'b0 ; endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (a) != (1'b0) && (b) != (1'b0) && (cin) != (1'b0) &&  (sum)  != (1'b1)  |->  (cout) != 1'b0 ; endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (a) != (1'b0) && (b) != (1'b0) && (cin) != (1'b0) &&  (sum)  != (1'b1)  &&  (cout)  != 1'b0  |->  (cout) ; endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (a) != (1'b0) && (b) != (1'b0) && (cin) != (1'b0) &&  (sum)  != (1'b1)  &&  (cout)  != 1'b0  |->  (cout) != 1'b0 ; endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (a) != (1'b0) && (b) != (1'b0) && (cin) != (1'b0) &&  (sum)  != (1'b1)  &&  (cout)  != 1'b0  |->  (cout) ; endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (a) != (1'b0) && (b) != (1'b0) && (cin) != (1'b0) &&  (sum)  != (1'b1)  &&  (cout)  != 1'b0  |->  (cout) != 1'b0 ; endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (a) != (1'b0) && (b) != (1'b0) && (cin) != (1'b0) &&  (sum)  != (1'b1)  &&  (cout)  != 1'b0  |->  (cout) ; endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (a) != (1'b0) && (b) != (1'b0) && (cin) != (1'b0) &&  (sum)  != (1'b1)  &&  (cout)  != 1'b0  |->  (cout) != 1'b0 ; endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (a) != (1'b0) && (b) != (1'b0) && (cin) != (1'b0) &&  (sum)  != (1'b1)  &&  (cout)  != 1'b0  |->  (cout) ; endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (a) != (1'b0) && (b) != (1'b0) && (cin) != (1'b0) &&  (sum)  != (1'b1)  &&  (cout)  != 1'b0  |->  (cout) != 1'b0 ; endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (a) != (1'b0) && (b) != (1'b0) && (cin) != (1'b0) &&  (sum)  != (1'b1)  &&  (cout)  != 1'b0  |->  (cout) ; endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (a) != (1'b0) && (b) != (1'b0) && (cin) != (1'b0) &&  (sum)  != (1'b1)  &&  (cout)  != 1'b0  |->  (cout) != 1'b0 ; endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (a) != (1'b0) && (b) != (1'b0) && (cin) != (1'b0) &&  (sum)  != (1'b1)  &&  (cout)  != 1'b0  |->  (cout) ; endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (a) != (1'b0) && (b) != (1'b0) && (cin) != (1'b0) &&  (sum)  != (1'b1)  &&  (cout)  != 1'b0  |->  (cout) != 1'b0 ; endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (a) != (1'b0) && (b) != (1'b0) && (cin) != (1'b0) &&  (sum)  != (1'b1)  &&  (cout)  != 1'b0  |->  (cout) ; endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (a) != (1'b0) && (b) != (1'b0) && (cin) != (1'b0) &&  (sum)  != (1'b1)  &&  (cout)  != 1'b0  |->  (cout) != 1'b0 ; endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (a) != (1'b0) && (b) != (1'b0) && (cin) != (1'b0) &&  (sum)  != (1'b1)  &&  (cout)  != 1'b0  |->  (cout) ; endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (a) != (1'b0) && (b) != (1'b0) && (cin) != (1'b0) &&  (sum)  != (1'b1)  &&  (cout)  != 1'b0  |->  (cout) != 1'b0 ; endproperty 
 
 property AddOneeotid; @(posedge clk_in_1)