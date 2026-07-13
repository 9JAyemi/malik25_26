property OddCheckeotid; @(posedge clk_in_1) (input_bits[0] == 1) |-> output_bits == 2'b01 ; endproperty 
 
 property EvenCheckeotid; @(posedge clk_in_1) (input_bits[0] != 1) |-> output_bits == 2'b10 ; endproperty 
 