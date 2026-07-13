property EnableSynceotid; @(posedge clk_enable_19) (in) == (4'b0000) |-> (out) == (ena ? 16'b1111111111111110 : 16'b1111111111111111); endproperty 
 
 property EnableSynceotid; @(posedge clk_enable_19) (in) == (4'b0001) |-> (out) == (ena ? 16'b1111111111111101 : 16'b1111111111111111); endproperty 
 
 property EnableSynceotid; @(posedge clk_enable_19) (in) == (4'b0010) |-> (out) == (ena ? 16'b1111111111111011 : 16'b1111111111111111); endproperty 
 
 property EnableSynceotid; @(posedge clk_enable_19) (in) == (4'b0011) |-> (out) == (ena ? 16'b1111111111110111 : 16'b1111111111111111); endproperty 
 
 property EnableSynceotid; @(posedge clk_enable_19) (in) == (4'b0100) |-> (out) == (ena ? 16'b1111111111101111 : 16'b1111111111111111); endproperty 
 
 property EnableSynceotid; @(posedge clk_enable_19) (in) == (4'b0101) |-> (out) == (ena ? 16'b1111111111011111 : 16'b1111111111111111); endproperty 
 
 property EnableSynceotid; @(posedge clk_enable_19) (in) == (4'b0110) |-> (out) == (ena ? 16'b1111111110111111 : 16'b1111111111111111); endproperty 
 
 property EnableSynceotid; @(posedge clk_enable_19) (in) == (4'b0111) |-> (out) == (ena ? 16'b1111111101111111 : 16'b1111111111111111); endproperty 
 
 property EnableSynceotid; @(posedge clk_enable_19) (in) == (4'b1000) |-> (out) == (ena ? 16'b1111111011111111 : 16'b1111111111111111); endproperty 
 
 property EnableSynceotid; @(posedge clk_enable_19) (in) == (4'b1001) |-> (out) == (ena ? 16'b1111110111111111 : 16'b1111111111111111); endproperty 
 
 property EnableSynceotid; @(posedge clk_enable_19) (in) == (4'b1010) |-> (out) == (ena ? 16'b1111101111111111 : 16'b1111111111111111); endproperty 
 
 property EnableSynceotid; @(posedge clk_enable_19) (in) == (4'b1011) |-> (out) == (ena ? 16'b1111011111111111 : 16'b1111111111111111); endproperty 
 
 property EnableSynceotid; @(posedge clk_enable_19) (in) == (4'b1100) |-> (out) == (ena ? 16'b1110111111111111 : 16'b1111111111111111); endproperty 
 
 property EnableSynceotid; @(posedge clk_enable_19) (in) == (4'b1101) |-> (out) == (ena ? 16'b1101111111111111 : 16'b1111111111111111); endproperty 
 
 property EnableSynceotid; @(posedge clk_enable_19) (in) == (4'b1110) |-> (out) == (ena ? 16'b1011111111111111 : 16'b1111111111111111); endproperty 
 
 property EnableSynceotid; @(posedge clk_enable_19) (in) == (4'b1111) |-> (out) == (ena ? 16'b0111111111111111 : 16'b1111111111111111); endproperty 
 
 property ValidIneotid; (in) != 4'bxxxx |-> (out) != 16'bxxxxxxxxxxxxxxxx; endproperty 
 