module and_gate_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic D1,
    input logic Y,
    input logic w1,
    input logic clk_in_1,
    input logic w2,
    input logic w3
);

property ValidIneotid; @(posedge clk_in_1) (Y) |-> (w3) && (w2) && (w1) && (A1) && (A2);endproperty
assert property (ValidIneotid);

property ValidIneotid_2; @(posedge clk_in_1) (w3) |-> (w2) && (B1);endproperty
assert property (ValidIneotid_2);

property ValidIneotid_3; @(posedge clk_in_1) (w2) |-> (w1) && (C1);endproperty
assert property (ValidIneotid_3);

property ValidIneotid_4; @(posedge clk_in_1) (w1) |-> (Y) && (D1);endproperty
assert property (ValidIneotid_4);

endmodule