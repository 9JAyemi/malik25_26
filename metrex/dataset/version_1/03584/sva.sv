// SVA for d_ff_en_clk_gate and TLATNTSCAX2TS
// Concise, focuses on the key clock-gating and flop-enable behaviors.

// Checker for the top module: gated DFF behavior and internal gate net
module d_ff_en_clk_gate_sva (
  input  logic        CLK,
  input  logic        EN,
  input  logic        TE,
  input  logic [31:0] DATA_IN,
  input  logic        DATA_OUT,
  input  logic        ENCLK
);
  // No-X on critical controls and observable outputs
  assert property (@(posedge CLK) !$isunknown({EN,TE,DATA_OUT}));
  assert property ((!(^ {EN,TE,CLK} === 1'bx)) |-> !$isunknown(ENCLK));

  // ENCLK must implement the expected AND-style clock gate: ENCLK = EN & TE & CLK
  // Sample on any edge of its inputs to catch combinational mismatches
  assert property (@(posedge CLK or negedge CLK or posedge EN or negedge EN or posedge TE or negedge TE)
                   ENCLK == (EN & TE & CLK));

  // When gate is closed at a posedge, output must hold
  assert property (@(posedge CLK) (!EN || !TE) |=> $stable(DATA_OUT));

  // Output may change only synchronously; ensure stable at negedge
  assert property (@(negedge CLK) $stable(DATA_OUT));

  // If output changes across a posedge, gate must be open
  assert property (@(posedge CLK) (DATA_OUT != $past(DATA_OUT)) |-> (EN && TE));

  // Coverage: observe gate open/closed and output activity
  cover property (@(posedge CLK) EN && TE);                 // gate open
  cover property (@(posedge CLK) !EN);                      // EN low
  cover property (@(posedge CLK) !TE);                      // TE low
  cover property (@(posedge CLK) EN && TE && $rose(DATA_OUT));
  cover property (@(posedge CLK) EN && TE && $fell(DATA_OUT));
  cover property (@(posedge CLK) EN && TE && ENCLK);        // ENCLK high at posedge
  cover property (@(posedge CLK) (!EN || !TE) && !ENCLK);   // ENCLK low at posedge
endmodule

// Checker for the clock-gate cell: pure combinational AND behavior and basic sanity
module tlatntscax2ts_sva (
  input logic E,
  input logic SE,
  input logic CK,
  input logic ECK
);
  // No-X propagation: if inputs known, output must be known
  assert property (!$isunknown({E,SE,CK}) |-> !$isunknown(ECK));

  // Functional equivalence: ECK = E & SE & CK
  assert property (@(posedge CK or negedge CK or posedge E or negedge E or posedge SE or negedge SE)
                   ECK == (E & SE & CK));

  // Sanity: CK low forces ECK low; CK high makes ECK == E & SE
  assert property (@(posedge CK or negedge CK or posedge E or negedge E or posedge SE or negedge SE)
                   (!CK) |-> (ECK == 1'b0));
  assert property (@(posedge CK or negedge CK or posedge E or negedge E or posedge SE or negedge SE)
                   (CK) |-> (ECK == (E & SE)));

  // Coverage: observe gate open/closed and edges on ECK
  cover property (@(posedge CK) E && SE && ECK);
  cover property (@(posedge CK) (!E || !SE) && !ECK);
  cover property (@(posedge CK) $rose(ECK));
  cover property (@(posedge CK) $fell(ECK));
endmodule

// Bind checkers to DUTs (binds can access internal ENCLK wire)
bind d_ff_en_clk_gate   d_ff_en_clk_gate_sva  u_dff_en_clk_gate_sva (.* , .ENCLK(ENCLK));
bind TLATNTSCAX2TS      tlatntscax2ts_sva     u_tlatntscax2ts_sva   (.*);