module full_adder_sva (
    input logic A,
    input logic B,
    input logic CIN,
    input logic COUT,
    input logic S,
    input logic clk_in_1
);

property AddOneeotid; @(posedge clk_in_1) (A) |-> (S) ;endproperty
assert property (AddOneeotid);

property AddOneeotid_2; @(posedge clk_in_1) (B) |-> (S) ;endproperty
assert property (AddOneeotid_2);

property AddOneeotid_3; @(posedge clk_in_1) (CIN) |-> (S) ;endproperty
assert property (AddOneeotid_3);

property AddOneeotid_4; @(posedge clk_in_1) (A) &&  (B) &&  (CIN) |-> (COUT) ;endproperty
assert property (AddOneeotid_4);

property AddOneeotid_5; @(posedge clk_in_1) (A) &&  (B) &&  ! (CIN) |-> ! (COUT) ;endproperty
assert property (AddOneeotid_5);

property AddOneeotid_6; @(posedge clk_in_1) (A) &&  ! (B) &&  (CIN) |-> ! (COUT) ;endproperty
assert property (AddOneeotid_6);

property AddOneeotid_7; @(posedge clk_in_1) ! (A) &&  (B) &&  (CIN) |-> ! (COUT) ;endproperty
assert property (AddOneeotid_7);

endmodule