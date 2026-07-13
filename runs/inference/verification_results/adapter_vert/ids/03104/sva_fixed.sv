module OR3_gate_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic X,
    input logic clk_osc_19
);

property OR3eotid; @(posedge clk_osc_19) (A) |-> (X) ;endproperty
assert property (OR3eotid);

property OR3eotid_2; @(posedge clk_osc_19) (B) |-> (X) ;endproperty
assert property (OR3eotid_2);

property OR3eotid_3; @(posedge clk_osc_19) (C) |-> (X) ;endproperty
assert property (OR3eotid_3);

endmodule