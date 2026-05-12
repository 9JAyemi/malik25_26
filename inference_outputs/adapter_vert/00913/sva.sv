property AddOneeotid; @(posedge clk) (a) + (b) == (adder_output) ; endproperty 
 
 property Compareeotid; @(posedge clk) (a) + (b) == (adder_output) && (a) > (b) |-> (comparator_output) == 3'b100 ; endproperty 
 
 property SyncEqeotid; @(posedge clk) (a) + (b) == (adder_output) && (a) != (b)  |-> (comparator_output) == 3'b001 ; endproperty 
 
 property yncEqeotid; @(posedge clk) (a) + (b) == (adder_output) && (a) == (b) |-> (comparator_output) == 3'b010 ; endproperty 
 
 property SyncCheckeotid; @(posedge clk) (ctrl) ?  (mux_output) ==  {1'b0, (comparator_output)}  :  (mux_output) ==  (adder_output) ; endproperty 
 