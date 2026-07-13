module eight_to_one_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1,
    input logic C2,
    input logic D1,
    input logic D2,
    input logic Y,
    input logic clk_in_1
);

property MaxAeotid; @(posedge clk_in_1) (A1) > (A2) |-> (Y) == (A1) ; endproperty
assert property (MaxAeotid);

property MaxBorMaxeotid; @(posedge clk_in_1) (A1) <= (A2) && (B1) > (B2) && (B1) > (Y) |-> (Y) == (B1) ; endproperty
assert property (MaxBorMaxeotid);

property MaxCgreaterthanYor; @(posedge clk_in_1) (A1) <= (A2) && (B1) <= (B2) && (C1) > (C2) && (C1) > (Y) |-> (Y) == (C1) ; endproperty
assert property (MaxCgreaterthanYor);

property MaxDgreaterthanor; @(posedge clk_in_1) (A1) <= (A2) && (B1) <= (B2) && (C1) <= (C2) && (D1) > (D2) && (D1) > (Y) |-> (Y) == (D1) ; endproperty
assert property (MaxDgreaterthanor);

property MaxDorMaxDor; @(posedge clk_in_1) (A1) <= (A2) && (B1) <= (B2) && (C1) <= (C2) &&  (D1) <= (D2)  |-> (Y) == (D2) ; endproperty
assert property (MaxDorMaxDor);

endmodule