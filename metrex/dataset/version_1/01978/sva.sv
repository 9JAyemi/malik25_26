// SVA for shift_register
module shift_register_sva (
  input logic        CLK,
  input logic        LOAD,
  input logic        RESET_B,
  input logic [3:0]  DATA_IN,
  input logic [3:0]  DATA_OUT,
  input logic        Q_N,
  input logic        DATAPATH_LOAD
);

  default clocking cb @(posedge CLK); endclocking

  // Combinational relationships
  assert property (@(posedge CLK or negedge RESET_B or posedge LOAD)
                   DATAPATH_LOAD == (RESET_B && LOAD));
  assert property (@(posedge CLK or negedge RESET_B)
                   Q_N == ~DATA_OUT[3]);

  // Clean outputs when not in reset
  assert property (RESET_B |-> !$isunknown({DATA_OUT,Q_N}));

  // Async active-low reset behavior
  assert property (@(posedge CLK or negedge RESET_B)
                   !RESET_B |-> (DATA_OUT == 4'b0000 && Q_N == 1'b1));
  assert property (!RESET_B |-> !DATAPATH_LOAD);

  // Hold when not loading
  assert property (disable iff(!RESET_B)
                   !LOAD |=> $stable(DATA_OUT));

  // Shift behavior when loading
  assert property (disable iff(!RESET_B)
                   LOAD |=> (DATA_OUT[0] == $past(DATA_IN[0])   &&
                             DATA_OUT[1] == $past(DATA_OUT[0]) &&
                             DATA_OUT[2] == $past(DATA_OUT[1]) &&
                             DATA_OUT[3] == $past(DATA_OUT[2])));

  // No X on serial input when loading
  assert property (disable iff(!RESET_B)
                   LOAD |-> !$isunknown(DATA_IN[0]));

  // Functional coverage
  cover property (@(posedge CLK) !RESET_B ##1 RESET_B); // reset pulse
  cover property (disable iff(!RESET_B) !LOAD ##1 LOAD ##1 !LOAD); // load toggle
  cover property (disable iff(!RESET_B)
                  LOAD[*3] ##1 (DATA_OUT[3] == $past(DATA_IN[0],3))); // bit propagates to MSB
endmodule

bind shift_register shift_register_sva u_shift_register_sva (
  .CLK(CLK),
  .LOAD(LOAD),
  .RESET_B(RESET_B),
  .DATA_IN(DATA_IN),
  .DATA_OUT(DATA_OUT),
  .Q_N(Q_N),
  .DATAPATH_LOAD(DATAPATH_LOAD)
);