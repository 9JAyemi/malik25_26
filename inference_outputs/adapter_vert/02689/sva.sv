property BitwiseAndeotid; @(posedge clk_in_1) ( A ) & ( B ) |-> ( and_res ) ; endproperty 
 
 property BitwiseOrEeotid; @(posedge clk_in_1) ( A ) | ( B ) |-> ( or_res ) ; endproperty 
 
 property BitwiseXOReotid; @(posedge clk_in_1) ( A ) ^ ( B ) |-> ( xor_res ) ; endproperty 
 
 property NotAeotid; @(posedge clk_in_1)  ( A )  !=  ( B )  |-> ( not_res ) ; endproperty 
 