property ZeroSynceotid; @(posedge clk_in_1) (input_val) == (10'b0000000000) |-> (binary_val) == 4'b0000 ; endproperty 
 
 property OneSynceotid; @(posedge clk_in_1) (input_val) == (10'b0000000001) |-> (binary_val) == 4'b0001 ; endproperty 
 
 property TwoSynceotid; @(posedge clk_in_1) (input_val) == (10'b0000000010) |-> (binary_val) == 4'b0010 ; endproperty 
 
 property ThreeSynceotid; @(posedge clk_in_1) (input_val) == (10'b0000000011) |-> (binary_val) == 4'b0011 ; endproperty 
 
 property FourSynceotid; @(posedge clk_in_1) (input_val) == (10'b0000000100) |-> (binary_val) == 4'b0100 ; endproperty 
 
 property FiveSynceotid; @(posedge clk_in_1) (input_val) == (10'b0000000101) |-> (binary_val) == 4'b0101 ; endproperty 
 
 property SixSynceotid; @(posedge clk_in_1) (input_val) == (10'b0000000110) |-> (binary_val) == 4'b0110 ; endproperty 
 
 property SevenSynceotid; @(posedge clk_in_1) (input_val) == (10'b0000000111) |-> (binary_val) == 4'b0111 ; endproperty 
 
 property EightSynceotid; @(posedge clk_in_1) (input_val) == (10'b0000001000) |-> (binary_val) == 4'b1000 ; endproperty 
 
 property NineSynceotid; @(posedge clk_in_1) (input_val) == (10'b0000001001) |-> (binary_val) == 4'b1001 ; endproperty 
 
 property ValidInputeotid; @(posedge clk_in_1) (input_val) != 10'b0000000000 && @(posedge clk_in_1) (input_val) != 10'b0000000001 && @(posedge clk_in_1) (input_val) != 10'b0000000010 && @(posedge clk_in_1) (input_val) != 10'b0000000011 && @(posedge clk_in_1) (input_val) != 10'b0000000100 && @(posedge clk_in_1) (input_val) != 10'b0000000101 && @(posedge clk_in_1) (input_val) != 10'b0000000110 && @(posedge clk_in_1) (input_val) != 10'b0000000111 && @(posedge clk_in_1) (input_val) != 10'b0000001000 && @(posedge clk_in_1) (input_val) != 10'b0000001001  |-> (binary_val) == 4'b0000; endproperty 
 