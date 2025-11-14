// SVA for the provided design. Bind these into your DUT.

////////////////////////////////////////
// priority_encoder
module pe_sva (input A,B,C,D, input [1:0] Y);
  // Functional correctness
  assert property (@(*) ({A,B,C,D}==4'b1110) |-> (Y==2'b11));
  assert property (@(*) ({A,B,C,D}==4'b1101) |-> (Y==2'b10));
  assert property (@(*) ({A,B,C,D}==4'b1011) |-> (Y==2'b01));
  assert property (@(*) ({A,B,C,D}==4'b0111) |-> (Y==2'b00));
  assert property (@(*) (!({A,B,C,D} inside {4'b1110,4'b1101,4'b1011,4'b0111})) |-> (Y==2'b00));
  // No Xs when inputs known
  assert property (@(*) !$isunknown({A,B,C,D}) |-> !$isunknown(Y));
  // Coverage
  cover property (@(*) {A,B,C,D}==4'b1110);
  cover property (@(*) {A,B,C,D}==4'b1101);
  cover property (@(*) {A,B,C,D}==4'b1011);
  cover property (@(*) {A,B,C,D}==4'b0111);
  cover property (@(*) !({A,B,C,D} inside {4'b1110,4'b1101,4'b1011,4'b0111}));
endmodule
bind priority_encoder pe_sva i_pe_sva (.A(A),.B(B),.C(C),.D(D),.Y(Y));

////////////////////////////////////////
// barrel_shifter
module bs_sva (input [3:0] data, input [1:0] shift, input [3:0] q);
  // Functional correctness (matches current RTL)
  assert property (@(*) (shift==2'b00) |-> (q==data));
  assert property (@(*) (shift==2'b01) |-> (q=={data[3:1],data[0]}));
  assert property (@(*) (shift==2'b10) |-> (q=={data[2:0],data[3]}));
  assert property (@(*) (shift==2'b11) |-> (q=={data[1:0],data[3:2]}));
  // No Xs when inputs known
  assert property (@(*) !$isunknown({data,shift}) |-> !$isunknown(q));
  // Coverage
  cover property (@(*) shift==2'b00);
  cover property (@(*) shift==2'b01);
  cover property (@(*) shift==2'b10);
  cover property (@(*) shift==2'b11);
endmodule
bind barrel_shifter bs_sva i_bs_sva (.data(data),.shift(shift),.q(q));

////////////////////////////////////////
// functional_module
module fm_sva (input [1:0] Y, input [3:0] data, input [3:0] q);
  // Bitwise OR with zero-extend of Y
  assert property (@(*) q == (data | {2'b00, Y}));
  // No Xs when inputs known
  assert property (@(*) !$isunknown({Y,data}) |-> !$isunknown(q));
  // Coverage
  cover property (@(*) Y==2'b00);
  cover property (@(*) Y==2'b01);
  cover property (@(*) Y==2'b10);
  cover property (@(*) Y==2'b11);
endmodule
bind functional_module fm_sva i_fm_sva (.Y(Y),.data(data),.q(q));

////////////////////////////////////////
// top_module (end-to-end q behavior = barrel_shifter(data,shift))
module top_sva (input A,B,C,D, input [3:0] data, input [1:0] shift, input [3:0] q);
  assert property (@(*) (shift==2'b00) |-> (q==data));
  assert property (@(*) (shift==2'b01) |-> (q=={data[3:1],data[0]}));
  assert property (@(*) (shift==2'b10) |-> (q=={data[2:0],data[3]}));
  assert property (@(*) (shift==2'b11) |-> (q=={data[1:0],data[3:2]}));
  assert property (@(*) !$isunknown({data,shift}) |-> !$isunknown(q));
  cover property (@(*) (shift inside {2'b00,2'b01,2'b10,2'b11}));
endmodule
bind top_module top_sva i_top_sva (.A(A),.B(B),.C(C),.D(D),.data(data),.shift(shift),.q(q));