module adder4_sva (
    input logic A,
    input logic B,
    input logic CIN,
    input logic COUT,
    input logic S,
    input logic b000000,
    input logic b000001,
    input logic b000010,
    input logic clk_in_1
);

property AdderSynceotid; @(posedge clk_in_1) (A) |-> (S) == (A + B + CIN); endproperty
assert property (AdderSynceotid);

property AdderSynceotid_2; @(posedge clk_in_1) (A) &&  (B) &&  (CIN) |-> (COUT) == 6'b000010 ; endproperty
assert property (AdderSynceotid_2);

property AdderSynceotid_3; @(posedge clk_in_1) (A) &&  (B) &&  (!CIN) |-> (COUT) == 6'b000001 ; endproperty
assert property (AdderSynceotid_3);

property AdderSynceotid_4; @(posedge clk_in_1) (A) &&  (!B) &&  (CIN) |-> (COUT) == 6'b000010 ; endproperty
assert property (AdderSynceotid_4);

property AdderSynceotid_5; @(posedge clk_in_1) (A) &&  (!B) &&  (!CIN) |-> (COUT) == 6'b000000 ; endproperty
assert property (AdderSynceotid_5);

property AdderSynceotid_6; @(posedge clk_in_1) (!A) &&  (B) &&  (CIN) |-> (COUT) == 6'b000010 ; endproperty
assert property (AdderSynceotid_6);

property AdderSynceotid_7; @(posedge clk_in_1) (!A) &&  (B) &&  (!CIN) |-> (COUT) == 6'b000001 ; endproperty
assert property (AdderSynceotid_7);

property AdderSynceotid_8; @(posedge clk_in_1) (!A) &&  (!B) &&  (CIN) |-> (COUT) == 6'b000010 ; endproperty
assert property (AdderSynceotid_8);

property AdderSynceotid_9; @(posedge clk_in_1) (!A) &&  (!B) &&  (!CIN) |-> (COUT) == 6'b000000 ; endproperty
assert property (AdderSynceotid_9);

endmodule