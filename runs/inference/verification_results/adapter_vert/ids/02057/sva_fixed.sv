module shift_register_sva (
    input logic in,
    input logic out,
    input logic register,
    input logic shift
);

property ShiftIneotid; @(posedge shift) (in) |-> (register == {in, register[7:1]}); endproperty
assert property (ShiftIneotid);

property ShiftOuteotid; @(posedge shift) (in) |-> (out == register[7]); endproperty
assert property (ShiftOuteotid);

endmodule