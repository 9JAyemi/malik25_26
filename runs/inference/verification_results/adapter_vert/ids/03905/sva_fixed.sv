module shift_register_sva (
    input logic clk,
    input logic data,
    input logic shifted_data
);

property ShiftIneotid; @(posedge clk) ( data ) |-> ( shifted_data  == {shifted_data[6:0], data[7]} ); endproperty
assert property (ShiftIneotid);

endmodule