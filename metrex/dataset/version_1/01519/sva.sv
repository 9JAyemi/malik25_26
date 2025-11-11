// SVA for priority_encoder
// Bind this file to the DUT; focuses on correctness, latency, priority, and pulse behavior.

module priority_encoder_sva (
  input  logic        clk,
  input  logic [7:0]  I,
  input  logic        EN,
  input  logic        V,
  input  logic [2:0]  Q,
  // internal regs
  input  logic [7:0]  I_reg,
  input  logic [7:0]  I_next,
  input  logic [2:0]  Q_reg,
  input  logic [2:0]  Q_next,
  input  logic [2:0]  Q_next_next,
  input  logic [2:0]  Q_next_next_next
);

  default clocking cb @(posedge clk); endclocking

  // simple past-valid flags
  logic past1_valid, past2_valid;
  always_ff @(posedge clk) begin
    past1_valid <= 1'b1;
    past2_valid <= past1_valid;
  end

  // priority encoder function (highest bit wins)
  function automatic logic [2:0] enc8 (input logic [7:0] x);
    if      (x[7]) enc8 = 3'b111;
    else if (x[6]) enc8 = 3'b110;
    else if (x[5]) enc8 = 3'b101;
    else if (x[4]) enc8 = 3'b100;
    else if (x[3]) enc8 = 3'b011;
    else if (x[2]) enc8 = 3'b010;
    else if (x[1]) enc8 = 3'b001;
    else           enc8 = 3'b000; // x[0]==1 case or x==0 (caller handles zero)
  endfunction

  // basic sanity (no X on outputs)
  assert property ( !$isunknown({EN,V,Q}) );

  // Input pipelining
  assert property (disable iff (!past1_valid) I_reg  == $past(I));
  assert property (disable iff (!past2_valid) I_next == $past(I,2));

  // Q pipeline sanity
  assert property (disable iff (!past1_valid) Q_next_next == $past(Q_next_next_next));
  assert property (disable iff (!past1_valid) Q_reg       == $past(Q_next_next));
  assert property (disable iff (!past1_valid) Q_next      == $past(Q_reg));
  assert property (Q == Q_next_next_next);

  // EN behavior (based on previous I_next)
  assert property (disable iff (!past1_valid) EN == ($past(I_next) != 8'b0));
  // Cross-check directly vs input latency
  assert property (disable iff (!past2_valid) EN == (|$past(I,2)));

  // V is a 1-cycle pulse (or toggles 1/0 if I_next remains nonzero)
  assert property (disable iff (!past1_valid) V == ( ($past(I_next)!=8'b0) && !$past(V) ));
  // If V is 1, EN must be 1 the same cycle
  assert property (V |-> EN);

  // Priority encoder correctness feeding Q_next_next_next
  // Uses previous I_next (due to sequential update semantics)
  assert property (disable iff (!past1_valid)
                   Q_next_next_next ==
                     ( ($past(I_next)!=8'b0) ? enc8($past(I_next)) : $past(Q_next) ));

  // Q output correctness (mirrors Q_next_next_next)
  assert property (disable iff (!past1_valid)
                   Q == ( ($past(I_next)!=8'b0) ? enc8($past(I_next)) : $past(Q_next) ));

  // Coverage: observe key scenarios
  // Any nonzero input causes EN=1 and a V pulse
  cover property (disable iff (!past1_valid)
                  ($past(I_next)!=8'b0) && !$past(V) ##1 (V && EN));

  // All-zero input case and pass-through from Q_next
  cover property (disable iff (!past1_valid)
                  ($past(I_next)==8'b0) && (Q == $past(Q_next)) && !V && !EN);

  // Highest-priority bit wins (bit7 overrides lower bits)
  cover property (disable iff (!past1_valid)
                  $past(I_next[7]) && (Q == 3'b111));

  // Mid priority example: bit3 selected when no higher bits set
  cover property (disable iff (!past1_valid)
                  !$past(|I_next[7:4]) && $past(I_next[3]) && (Q == 3'b011));

  // Lowest priority example: bit0 selected when no higher bits set
  cover property (disable iff (!past1_valid)
                  !$past(|I_next[7:1]) && $past(I_next[0]) && (Q == 3'b000));

  // Persistent nonzero input causes V to toggle 1->0->1...
  cover property (disable iff (!past1_valid)
                  ($past(I_next)!=8'b0) ##1 ($past(I_next)!=8'b0) and (V==0) ##1 (V==1));

endmodule

// Bind to DUT
bind priority_encoder priority_encoder_sva sva (
  .clk                (clk),
  .I                  (I),
  .EN                 (EN),
  .V                  (V),
  .Q                  (Q),
  .I_reg              (I_reg),
  .I_next             (I_next),
  .Q_reg              (Q_reg),
  .Q_next             (Q_next),
  .Q_next_next        (Q_next_next),
  .Q_next_next_next   (Q_next_next_next)
);