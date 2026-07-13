module four_input_and_sva (
    input logic A1,
    input logic A2,
    input logic B1_N,
    input logic C1,
    input logic X,
    input logic and2_out,
    input logic clk_in_1
);

property ValidIneotid; @(posedge clk_in_1) (A1) && (A2) &&  ( !B1_N ) |->  (X) ;endproperty
assert property (ValidIneotid);

property ValidIneotid_2; @(posedge clk_in_1) (A1) && (A2) &&  ( C1 ) |->  (and2_out) ;endproperty
assert property (ValidIneotid_2);

property ValidIneotid_3; @(posedge clk_in_1) (A1) && (A2) &&  ( !B1_N ) &&  ( C1 ) |->  (X) ;endproperty
assert property (ValidIneotid_3);

endmodule