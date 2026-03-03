// Bindable SVA for AddressGenerator
module AddressGenerator_sva
(
  input  logic        clk,
  input  logic        ce,
  input  logic [4:0]  Operation,
  input  logic [1:0]  MuxCtrl,
  input  logic [7:0]  DataBus, T, X, Y,
  input  logic [15:0] AX,
  input  logic        Carry,
  // Internal DUT state
  input  logic [7:0]  AL, AH,
  input  logic        SavedCarry
);

  default clocking cb @(posedge clk); endclocking

  // Past-valid guard
  logic past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Decodes and combinational helpers (current cycle)
  let ALCtrl = Operation[4:2];
  let AHCtrl = Operation[1:0];
  let sum9   = {1'b0, (MuxCtrl[1] ? T  : AL)} + {1'b0, (MuxCtrl[0] ? Y : X)};
  let tmpval = (!AHCtrl[1] | SavedCarry);
  let tmpadd = (AHCtrl[1] ? AH : AL) + {7'b0, tmpval};

  // Structural correctness
  assert property (AX == {AH, AL});
  assert property (Carry == sum9[8]);

  // State hold when ce==0
  assert property (past_valid && !ce |=> (AL == $past(AL) && AH == $past(AH) && SavedCarry == $past(SavedCarry)));

  // SavedCarry update
  assert property (past_valid && ce |=> SavedCarry == $past(Carry));

  // AL update behavior
  // Hold when ALCtrl[2]==0
  assert property (past_valid && ce && !$past(Operation[4]) |=> AL == $past(AL));
  // ALCtrl[2:0] == 3'b100: AL <= NewAL (sum9[7:0])
  assert property (past_valid && ce && $past(Operation[4:2]) == 3'b100 |=> 
                   AL == ({1'b0, ($past(MuxCtrl[1]) ? $past(T)  : $past(AL))} + 
                          {1'b0, ($past(MuxCtrl[0]) ? $past(Y) : $past(X))})[7:0]);
  // 3'b101: AL <= DataBus
  assert property (past_valid && ce && $past(Operation[4:2]) == 3'b101 |=> AL == $past(DataBus));
  // 3'b110: AL <= TmpAdd
  assert property (past_valid && ce && $past(Operation[4:2]) == 3'b110 |=> 
                   AL == (( $past(Operation[1]) ? $past(AH) : $past(AL)) + 
                          {7'b0, (! $past(Operation[1]) | $past(SavedCarry))}));
  // 3'b111: AL <= T
  assert property (past_valid && ce && $past(Operation[4:2]) == 3'b111 |=> AL == $past(T));

  // AH update behavior (always under ce)
  // 2'b00: hold
  assert property (past_valid && ce && $past(Operation[1:0]) == 2'b00 |=> AH == $past(AH));
  // 2'b01: zero
  assert property (past_valid && ce && $past(Operation[1:0]) == 2'b01 |=> AH == 8'h00);
  // 2'b10: TmpAdd
  assert property (past_valid && ce && $past(Operation[1:0]) == 2'b10 |=> 
                   AH == (( $past(Operation[1]) ? $past(AH) : $past(AL)) + 
                          {7'b0, (! $past(Operation[1]) | $past(SavedCarry))}));
  // 2'b11: DataBus
  assert property (past_valid && ce && $past(Operation[1:0]) == 2'b11 |=> AH == $past(DataBus));

  // Functional coverage (concise)
  // AL write select cases
  cover property (ce && ALCtrl[2] && (ALCtrl[1:0] == 2'b00));
  cover property (ce && ALCtrl[2] && (ALCtrl[1:0] == 2'b01));
  cover property (ce && ALCtrl[2] && (ALCtrl[1:0] == 2'b10));
  cover property (ce && ALCtrl[2] && (ALCtrl[1:0] == 2'b11));
  cover property (ce && !ALCtrl[2]); // AL hold via control

  // AH write select cases
  cover property (ce && (AHCtrl == 2'b00));
  cover property (ce && (AHCtrl == 2'b01));
  cover property (ce && (AHCtrl == 2'b10));
  cover property (ce && (AHCtrl == 2'b11));

  // MuxCtrl combinations exercised
  cover property (MuxCtrl == 2'b00);
  cover property (MuxCtrl == 2'b01);
  cover property (MuxCtrl == 2'b10);
  cover property (MuxCtrl == 2'b11);

  // Carry generation/no-carry observed
  cover property (Carry == 1'b1);
  cover property (Carry == 1'b0);

  // TmpAdd path exercised with/without SavedCarry contribution
  cover property (ce && (AHCtrl == 2'b10) && (SavedCarry == 1'b1));
  cover property (ce && (AHCtrl == 2'b10) && (SavedCarry == 1'b0));

  // Global hold via ce==0
  cover property (!ce);

endmodule

// Example bind (connects to internals AL/AH/SavedCarry)
bind AddressGenerator AddressGenerator_sva sva_addrgen (
  .clk(clk), .ce(ce), .Operation(Operation), .MuxCtrl(MuxCtrl),
  .DataBus(DataBus), .T(T), .X(X), .Y(Y), .AX(AX), .Carry(Carry),
  .AL(AL), .AH(AH), .SavedCarry(SavedCarry)
);