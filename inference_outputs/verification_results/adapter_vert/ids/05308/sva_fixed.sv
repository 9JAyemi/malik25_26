module four_bit_adder_sva (
    input logic A,
    input logic B,
    input logic a,
    input logic b,
    input logic temp_carry,
    input logic temp_sum,
    input logic b0,
    input logic clk_in_1
);

property AddOneeotid; @(posedge clk_in_1) (A) |-> (temp_sum) ;endproperty
assert property (AddOneeotid);

property AddOneeotid_2; @(posedge clk_in_1) (B) |-> (temp_sum) ;endproperty
assert property (AddOneeotid_2);

property AddOneeotid_3; @(posedge clk_in_1) (A) &&  (B) &&  ( 1'b0 ) |-> (temp_sum) == (a ) &&  (temp_carry) == (b ) ;endproperty
assert property (AddOneeotid_3);

property AddOneeotid_4; @(posedge clk_in_1) (A) &&  ( 1'b0 ) &&  (B) |-> (temp_sum) == (a ) &&  (temp_carry) == (b ) ;endproperty
assert property (AddOneeotid_4);

property AddOneeotid_5; @(posedge clk_in_1) ( 1'b0 ) &&  (A) &&  (B) |-> (temp_sum) == (a ) &&  (temp_carry) == (b ) ;endproperty
assert property (AddOneeotid_5);

property AddOneeotid_6; @(posedge clk_in_1) ( 1'b0 ) &&  ( 1'b0 ) &&  ( 1'b0 ) |-> (temp_sum) == (a ) &&  (temp_carry) == (b ) ;endproperty
assert property (AddOneeotid_6);

endmodule