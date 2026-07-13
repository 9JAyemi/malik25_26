property ZeroSynceotid; @(posedge clk_in_1) (in_value) == (4'b0000) |-> (out_value) == 4'b0000 ; endproperty 
 
 property OneSynceotid; @(posedge clk_in_1) (in_value) == (4'b0001) |-> (out_value) == 4'b0001 ; endproperty 
 
 property TwoSynceotid; @(posedge clk_in_1) (in_value) == (4'b0010) |-> (out_value) == 4'b0010 ; endproperty 
 
 property ThreeSynceotid; @(posedge clk_in_1) (in_value) == (4'b0011) |-> (out_value) == 4'b0011 ; endproperty 
 
 property FourSynceotid; @(posedge clk_in_1) (in_value) == (4'b0100) |-> (out_value) == 4'b0100 ; endproperty 
 
 property FiveSynceotid; @(posedge clk_in_1) (in_value) == (4'b0101) |-> (out_value) == 4'b0101 ; endproperty 
 
 property SixSynceotid; @(posedge clk_in_1) (in_value) == (4'b0110) |-> (out_value) == 4'b0110 ; endproperty 
 
 property SevenSynceotid; @(posedge clk_in_1) (in_value) == (4'b0111) |-> (out_value) == 4'b0111 ; endproperty 
 
 property EightSynceotid; @(posedge clk_in_1) (in_value) == (4'b1000) |-> (out_value) == 4'b1000 ; endproperty 
 
 property NineSynceotid; @(posedge clk_in_1) (in_value) == (4'b1001) |-> (out_value) == 4'b1001 ; endproperty 
 
 property ValidInputeotid; @(posedge clk_in_1) (in_value) != 4'bxxxx  |-> (out_value) != 4'bxxxx ; endproperty 
 