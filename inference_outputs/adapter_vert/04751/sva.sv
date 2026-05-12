property BitwiseAndeotid; @(posedge clk_in_17) (a) && (b) |-> (result) == (and_result); endproperty 
 
 property BitwiseAndeotid; @(posedge clk_in_17) (a) && (b) &&  (  result != and_result  ) |-> $error("InvalidDataeotid"); endproperty 
 