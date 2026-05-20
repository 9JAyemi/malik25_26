module alu_sva (
    input logic ALU_MODE,
    input logic CIN,
    input logic COUT,
    input logic I0,
    input logic I1,
    input logic I3,
    input logic SUM,
    input logic b0,
    input logic b0000,
    input logic b0001,
    input logic b0010,
    input logic b0011,
    input logic b0100,
    input logic b0101,
    input logic b0110,
    input logic b0111,
    input logic b1,
    input logic b1000,
    input logic b1001,
    input logic b111x,
    input logic clk_in_1
);

property AddSynceotid; @(posedge clk_in_1) (ALU_MODE) == (4'b0000) |-> (SUM) == (I0 ^ I1 ^ CIN) && (COUT) == ( (I0 & I1) | (CIN & (I0 ^ I1)) ); endproperty
assert property (AddSynceotid);

property SubSynceotid; @(posedge clk_in_1) (ALU_MODE) == (4'b0001) |-> (SUM) == (I0 ^ I1 ^ CIN) && (COUT) == ( (~I0 & I1) | (CIN & (~I0 ^ I1)) ); endproperty
assert property (SubSynceotid);

property AddSubeotid; @(posedge clk_in_1) (ALU_MODE) == (4'b0010) && (  (I3)  ) |-> (SUM) == (I0 ^ I1 ^ CIN) && (COUT) == ( (I0 & I1) | (CIN & (I0 ^ I1)) ); endproperty
assert property (AddSubeotid);

property Subeotid; @(posedge clk_in_1) (ALU_MODE) == (4'b0010) &&  ( !(  (I3)  )  ) |-> (SUM) == (I0 ^ I1 ^ CIN) && (COUT) == ( (~I0 & I1) | (CIN & (~I0 ^ I1)) ); endproperty
assert property (Subeotid);

property ALUeotid; @(posedge clk_in_1) (ALU_MODE) == (4'b0011) |-> (SUM) == ( ~(I0 ^ I1) ) && (COUT) == ( 1'b1 ) ; endproperty
assert property (ALUeotid);

property ALUeotid_2; @(posedge clk_in_1) (ALU_MODE) == (4'b0100) |-> (SUM) == ( ~(I0 ^ I1) ) && (COUT) == ( (~I0 & I1) | (CIN & (~I0 ^ I1)) ); endproperty
assert property (ALUeotid_2);

property ALUeotid_3; @(posedge clk_in_1) (ALU_MODE) == (4'b0101) |-> (SUM) == ( ~(I0 ^ I1) ) && (COUT) == ( (I0 & I1) | (CIN & (I0 | I1)) ); endproperty
assert property (ALUeotid_3);

property ALUeotid_4; @(posedge clk_in_1) (ALU_MODE) == (4'b0110) |-> (SUM) == ( I0 ) && (COUT) == ( 1'b0 ) ; endproperty
assert property (ALUeotid_4);

property ALUeotid_5; @(posedge clk_in_1) (ALU_MODE) == (4'b0111) |-> (SUM) == ( ~I0 ) && (COUT) == ( 1'b1 ) ; endproperty
assert property (ALUeotid_5);

property ALUeotid_6; @(posedge clk_in_1) (ALU_MODE) == (4'b1000) && (  (I3)  ) |-> (SUM) == ( I0 ) && (COUT) == ( 1'b0 ) ; endproperty
assert property (ALUeotid_6);

property ALUeotid_7; @(posedge clk_in_1) (ALU_MODE) == (4'b1000) &&  ( !(  (I3)  )  ) |-> (SUM) == ( ~I0 ) && (COUT) == ( 1'b1 ) ; endproperty
assert property (ALUeotid_7);

property ALUeotid_8; @(posedge clk_in_1) (ALU_MODE) == (4'b1001) |-> (SUM) == ( I0 & I1 ) && (COUT) == ( I0 & I1 ); endproperty
assert property (ALUeotid_8);

property ValidOpseotid; (ALU_MODE) != 4'b111x  |-> (SUM) != 1'b0 && (COUT) != 1'b0; endproperty
assert property (ValidOpseotid);

endmodule