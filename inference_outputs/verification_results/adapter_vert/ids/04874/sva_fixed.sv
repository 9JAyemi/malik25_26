module and_gate_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic Y,
    input logic clk_in_1
);

property ValidOnRiseeotid; @(posedge clk_in_1) (A) && (B) && (C) |-> (Y) ;endproperty
assert property (ValidOnRiseeotid);

property ValidOnRiseeotid_2; @(posedge clk_in_1) (A) && (B) && (!C) |-> !(Y) ;endproperty
assert property (ValidOnRiseeotid_2);

property ValidOnRiseeotid_3; @(posedge clk_in_1) (A) && (!B) && (C) |-> !(Y) ;endproperty
assert property (ValidOnRiseeotid_3);

property ValidOnRiseeotid_4; @(posedge clk_in_1) (A) && (!B) && (!C) |-> !(Y) ;endproperty
assert property (ValidOnRiseeotid_4);

property ValidOnRiseeotid_5; @(posedge clk_in_1) (!A) && (B) && (C) |-> !(Y) ;endproperty
assert property (ValidOnRiseeotid_5);

property ValidOnRiseeotid_6; @(posedge clk_in_1) (!A) && (B) && (!C) |-> !(Y) ;endproperty
assert property (ValidOnRiseeotid_6);

property ValidOnRiseeotid_7; @(posedge clk_in_1) (!A) && (!B) && (C) |-> !(Y) ;endproperty
assert property (ValidOnRiseeotid_7);

property ValidOnRiseeotid_8; @(posedge clk_in_1) (!A) && (!B) && (!C) |-> !(Y) ;endproperty
assert property (ValidOnRiseeotid_8);

endmodule