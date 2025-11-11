// SVA for Shift_Register
module shift_register_sva (
  input  logic        CLK,
  input  logic        EN,
  input  logic        TE,
  input  logic [6:0]  DATA_IN,
  input  logic [6:0]  DATA_OUT,
  input  logic        ENCLK,

  // internal signals
  input  logic [6:0]  data_out_reg,
  input  logic [6:0]  data_out
);
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge CLK) past_valid <= 1'b1;

  default clocking cb @(posedge CLK); endclocking

  // Shift behavior
  assert property (disable iff (!past_valid)
    EN |=> data_out_reg == { $past(DATA_IN[6]), $past(data_out_reg[6:1]) });

  // Hold when EN=0
  assert property (disable iff (!past_valid)
    !EN |=> data_out_reg == $past(data_out_reg));

  // TE transparency and latch-hold
  assert property (disable iff (!past_valid)
    TE |-> (data_out == data_out_reg));

  assert property (disable iff (!past_valid)
    !TE |=> data_out == $past(data_out));

  // Output wiring
  assert property (disable iff (!past_valid)
    DATA_OUT == data_out);

  assert property (disable iff (!past_valid)
    ENCLK == DATA_OUT[0]);

  // Output-level functional check (only using I/O): visible shift when TE holds high
  assert property (disable iff (!past_valid)
    (TE && EN) |=> (TE && (DATA_OUT == { $past(DATA_IN[6]), $past(DATA_OUT[6:1]) })));

  // Output holds when EN=0 and TE=1
  assert property (disable iff (!past_valid)
    (TE && !EN) |=> (TE && (DATA_OUT == $past(DATA_OUT))));

  // No X/Z on outputs after warmup
  assert property (disable iff (!past_valid)
    !$isunknown(DATA_OUT) && !$isunknown(ENCLK));

  // Coverage
  cover property (past_valid && EN);                      // saw a shift
  cover property (past_valid && TE);                      // TE transparent observed
  cover property (past_valid ##1 (TE && EN)[*7]);         // 7 consecutive transparent shifts
  cover property (past_valid ##1 !TE ##1 !TE ##1 TE);     // latch close-open sequence
  cover property (past_valid ##1 $rose(ENCLK));
  cover property (past_valid ##1 $fell(ENCLK));
endmodule

bind Shift_Register shift_register_sva u_shift_register_sva (
  .CLK         (CLK),
  .EN          (EN),
  .TE          (TE),
  .DATA_IN     (DATA_IN),
  .DATA_OUT    (DATA_OUT),
  .ENCLK       (ENCLK),
  .data_out_reg(data_out_reg),
  .data_out    (data_out)
);

// Minimal, behavior-agnostic SVA for TLATNTSCAX2TS (behavior not defined in DUT)
module tlatntscax2ts_sva (
  input logic CK,
  input logic E,
  input logic SE,
  input logic ECK
);
  // No X on observable output
  assert property (!$isunknown(ECK));

  // Output only changes when an input changes
  assert property ($changed(ECK) |-> ($changed(CK) || $changed(E) || $changed(SE)));

  // Coverage
  cover property ($rose(E));
  cover property ($rose(SE));
  cover property ($rose(ECK));
  cover property ($fell(ECK));
endmodule

bind TLATNTSCAX2TS tlatntscax2ts_sva u_tlatntscax2ts_sva (
  .CK (CK),
  .E  (E),
  .SE (SE),
  .ECK(ECK)
);