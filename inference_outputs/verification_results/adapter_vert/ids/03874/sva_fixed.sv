module NAND4AND2_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic Z,
    input logic nand1_out,
    input logic nand2_out,
    input logic nand3_out,
    input logic b01,
    input logic b0x,
    input logic b10,
    input logic clk_in_1
);

property SyncIneotid; @(negedge clk_in_1) (A) and (B) |-> nand1_out == 2'b0x ;endproperty
assert property (SyncIneotid);

property SyncIneotid_2; @(negedge clk_in_1) (C) and (D) |-> nand2_out == 2'b0x ;endproperty
assert property (SyncIneotid_2);

property SyncIneotid_3; @(negedge clk_in_1) (nand1_out) and (nand2_out) |-> nand3_out == 2'b0x ;endproperty
assert property (SyncIneotid_3);

property SyncIneotid_4; @(negedge clk_in_1) (nand3_out) and (nand3_out) |-> Z == 2'b10 ;endproperty
assert property (SyncIneotid_4);

property SyncIneotid_5; @(negedge clk_in_1) (Z) and (Z) |-> Z == 2'b01 ;endproperty
assert property (SyncIneotid_5);

endmodule