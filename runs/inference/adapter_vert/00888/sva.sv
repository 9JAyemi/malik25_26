property BitwiseAndeotid; @(posedge clk_in_1) ( in1 ) && (  in2 ) |-> ( and1 ) ; endproperty 
 
 property BitwiseOrEeotid; @(posedge clk_in_1) ( in1 ) || (  in2 ) |-> ( or1 ) ; endproperty 
 
 property BitwiseXorEeotid; @(posedge clk_in_1) ( in1 ) != (  in2 ) |-> ( xor1 ) ; endproperty 
 
 property AndSynceotid; @(posedge clk_in_1) ( in1 ) && (  in2 ) && (  in3 ) |-> ( and2 ) ; endproperty 
 
 property OrSynceotid; @(posedge clk_in_1) ( in1 ) || (  in2 ) || (  in3 ) |-> ( or2 ) ; endproperty 
 
 property XorSynceotid; @(posedge clk_in_1) ( in1 ) != (  in2 ) && (  in3 ) |-> ( xor2 ) ; endproperty 
 
 property AndSynceotid; @(posedge clk_in_1) ( in1 ) && (  in2 ) && (  in3 ) && (  in4 ) |-> ( and3 ) ; endproperty 
 
 property OrSynceotid; @(posedge clk_in_1) ( in1 ) || (  in2 ) || (  in3 ) || (  in4 ) |-> ( or3 ) ; endproperty 
 
 property XorSynceotid; @(posedge clk_in_1) ( in1 ) != (  in2 ) && (  in3 ) && (  in4 ) |-> ( xor3 ) ; endproperty 
 
 