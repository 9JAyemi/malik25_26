property BinaryToGrayeotid; @(posedge clk_in_17) (binary) |-> (gray) == (binary); endproperty 
 
 property GraySynceotid; @(posedge clk_in_17) (binary) |-> (gray) == ( { binary[3], binary[2] ^ binary[3], binary[1] ^ binary[2], binary[0] ^ binary[1] } ); endproperty 
 
 property GraySynceotid; @(posedge clk_in_17) (binary) |-> (gray) == ( { binary[3], binary[2] ^ binary[3], binary[1] ^ binary[2], binary[0] ^ binary[1] } ); endproperty 
 