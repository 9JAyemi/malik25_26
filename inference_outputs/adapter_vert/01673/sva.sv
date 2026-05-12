property ResetSynceotid; @(posedge clk) (rst) |-> (state == S0) && (out == O0) ;endproperty 
 
 property ResetSynceotid; @(posedge clk) (rst) && (in == I0) |-> (state == S1) && (out == O0) ;endproperty 
 
 property ResetSynceotid; @(posedge clk) (rst) && (in == I1) |-> (state == S2) && (out == O1) ;endproperty 
 
 property ResetSynceotid; @(posedge clk) (rst) && (  (in != I0) &&  (in != I1)  ) |-> (state == S0) && (out == O0) ;endproperty 
 
 property ResetSynceotid; @(posedge clk) ! (rst) && (in == I0) |-> (state == S2) && (out == O0) ;endproperty 
 
 property ResetSynceotid; @(posedge clk) ! (rst) && (in == I1) |-> (state == S3) && (out == O1) ;endproperty 
 
 property ResetSynceotid; @(posedge clk) ! (rst) && (  (in != I0) &&  (in != I1)  ) |-> (state == S1) && (out == O0) ;endproperty 
 
 