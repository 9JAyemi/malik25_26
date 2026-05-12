property AddSynceotid; @(posedge clk_in_17) ( !SIGN_EXT ) |-> o == a + b + c ; endproperty 
 
 property AddSynceotid; @(posedge clk_in_17) ( SIGN_EXT ) |-> o == {a[WIDTH-1],a[WIDTH-1],a} + {b[WIDTH-1],b[WIDTH-1],b} + {c[WIDTH-1],c[WIDTH-1],c} ; endproperty 
 