module and4_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic X,
    input logic and0_out,
    input logic and1_out,
    input logic clk_in_19
);

property ValidInputeotid; @(posedge clk_in_19) (A) && (B) |-> (and0_out) ;endproperty
assert property (ValidInputeotid);

property ValidInputeotid_2; @(posedge clk_in_19) (C) && (D) |-> (and1_out) ;endproperty
assert property (ValidInputeotid_2);

property ValidInputeotid_3; @(posedge clk_in_19) (and0_out) && (and1_out) |-> (X) ;endproperty
assert property (ValidInputeotid_3);

endmodule