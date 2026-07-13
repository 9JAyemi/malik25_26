property ShiftSynceotid; @(posedge clk_in_1) (shift_amt) == (2'b00) |-> (out) == (in); endproperty 
 
 property ShiftRighteotid; @(posedge clk_in_1) (shift_amt) == (2'b01) &&  ( dir ) |-> (out) == ({in[2:0], in[3]}); endproperty 
 
 property ShiftRighteotid; @(posedge clk_in_1) (shift_amt) == (2'b01) &&  ( !(dir) ) |-> (out) == ({in[1:0], in[3:2]}); endproperty 
 
 property ShiftLefteotid; @(posedge clk_in_1) (shift_amt) == (2'b10) &&  ( !(dir) ) |-> (out) == ({in[1:0], in[3:2]}); endproperty 
 
 property ShiftLefteotid; @(posedge clk_in_1) (shift_amt) == (2'b10) &&  (  (dir) ) |-> (out) == ({in[2:0], in[3]}); endproperty 
 
 property ShiftOneeotid; @(posedge clk_in_1) (shift_amt) == (2'b11) |-> (out) == ({in[0], in[3:1]}); endproperty 
 