property ShiftIneotid; @(posedge shift) (in) |-> (register == {in, register[7:1]}); endproperty 
 
 property ShiftOuteotid; @(posedge shift) (in) |-> (out == register[7]); endproperty 
 