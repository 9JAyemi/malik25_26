property AddSynceotid; @(posedge clk_in_1) (select) |-> (sum) == (adder_out); endproperty 
 
 property ValidDataeotid; @(posedge clk_in_1) (select) &&  (  ! (  a  &&  b  &&  cfg_16 ) ) |-> (sum) == (mux_out); endproperty 
 
 property AdderSynceotid; @(posedge clk_in_1) (  a  &&  b  &&  cfg_16 ) |-> (sum) == (  a  +  b  +  1'b0 ); endproperty 
 