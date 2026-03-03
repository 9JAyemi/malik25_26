// SVA checker for decoder_4_to_16
module decoder_4_to_16_sva (
  input logic [1:0]  AB,
  input logic [15:0] Y
);

  // Inputs/outputs must be 2-state
  assert property (@(AB or Y) !$isunknown(AB)) else $error("AB has X/Z");
  assert property (@(AB or Y) !$isunknown(Y))  else $error("Y has X/Z");

  // Output shape: only one of Y[3:0] is 1, upper bits must be 0
  assert property (@(AB or Y) 1'b1 |-> ##0 $onehot(Y[3:0]))
    else $error("Y[3:0] not onehot");
  assert property (@(AB or Y) 1'b1 |-> ##0 (Y[15:4] == '0))
    else $error("Y[15:4] not zero");

  // Forward decode: AB -> Y
  assert property (@(AB or Y) (AB==2'b00) |-> ##0 (Y==16'h0001))
    else $error("AB=00 did not produce Y=0001");
  assert property (@(AB or Y) (AB==2'b01) |-> ##0 (Y==16'h0002))
    else $error("AB=01 did not produce Y=0002");
  assert property (@(AB or Y) (AB==2'b10) |-> ##0 (Y==16'h0004))
    else $error("AB=10 did not produce Y=0004");
  assert property (@(AB or Y) (AB==2'b11) |-> ##0 (Y==16'h0008))
    else $error("AB=11 did not produce Y=0008");

  // Reverse decode: Y -> AB (no aliasing)
  assert property (@(AB or Y) (Y==16'h0001) |-> ##0 (AB==2'b00))
    else $error("Y=0001 not paired with AB=00");
  assert property (@(AB or Y) (Y==16'h0002) |-> ##0 (AB==2'b01))
    else $error("Y=0002 not paired with AB=01");
  assert property (@(AB or Y) (Y==16'h0004) |-> ##0 (AB==2'b10))
    else $error("Y=0004 not paired with AB=10");
  assert property (@(AB or Y) (Y==16'h0008) |-> ##0 (AB==2'b11))
    else $error("Y=0008 not paired with AB=11");

  // Coverage: all decode cases observed
  cover property (@(AB or Y) (AB==2'b00) ##0 (Y==16'h0001));
  cover property (@(AB or Y) (AB==2'b01) ##0 (Y==16'h0002));
  cover property (@(AB or Y) (AB==2'b10) ##0 (Y==16'h0004));
  cover property (@(AB or Y) (AB==2'b11) ##0 (Y==16'h0008));

endmodule

// Bind into DUT
bind decoder_4_to_16 decoder_4_to_16_sva dec_sva (.AB(AB), .Y(Y));