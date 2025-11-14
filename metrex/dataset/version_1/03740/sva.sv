// SVA for fir_mul_32s_32s_3bkb_MulnS_0
// Bind this file to the DUT. Focus: reset behavior, CE gating, latency, arithmetic correctness, stability, X checks, and coverage.

module fir_mul_32s_32s_3bkb_MulnS_0_sva;

  // Infer widths from bound instance
  localparam int W = $bits(p);
  localparam int PW = 2*W;

  // Handy constants and helpers
  localparam signed [W-1:0] S_MIN = {1'b1,{(W-1){1'b0}}};
  localparam signed [W-1:0] S_MAX = {1'b0,{(W-1){1'b1}}};

  function automatic signed [W-1:0] trunc_prod(input signed [W-1:0] x, input signed [W-1:0] y);
    logic signed [PW-1:0] tmp;
    begin
      tmp = x * y;
      trunc_prod = tmp[W-1:0];
    end
  endfunction

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Sanity/X checks on critical control and data
  assert property ( !$isunknown({clk,reset}) );
  assert property ( !ce || (!$isunknown(ce) && !$isunknown(a) && !$isunknown(b)) );

  // p must reflect p_reg (continuous assign integrity)
  assert property ( p == p_reg );

  // Reset clears all regs and output
  assert property ( reset |-> ##0 (a_reg==0 && b_reg==0 && p_reg==0 && p==0) );

  // CE gating: when ce=0, nothing changes on this edge
  assert property ( !ce |-> ##0 (a_reg==$past(a_reg) && b_reg==$past(b_reg) && p_reg==$past(p_reg) && p==$past(p)) );

  // CE update: on ce=1, a_reg/b_reg take a/b; p_reg takes product of previous a_reg/b_reg (all in same edge)
  assert property ( ce |-> ##0 (a_reg==a && b_reg==b && p_reg==trunc_prod($past(a_reg),$past(b_reg))) );

  // First CE after coming out of reset produces zero (previous regs were zero)
  assert property ( $rose(!reset) ##[1:$] ce |-> ##0 (p==0 && p_reg==0) );

  // Back-to-back CE correctness vs external inputs: 2-cycle latency from a/b to p when CE stays high
  assert property ( ce && $past(ce) |-> ##0 (p == trunc_prod($past(a),$past(b))) );

  // General CE-to-next-CE latency correctness vs external inputs (handles gaps in CE)
  property next_ce_latency_correct;
    logic signed [W-1:0] as, bs;
    (ce, as = a, bs = b) |-> ##[1:$] (ce ##0 (p == trunc_prod(as, bs)));
  endproperty
  assert property ( next_ce_latency_correct );

  // Output only updates on CE (i.e., changes in p imply CE this cycle)
  assert property ( (p != $past(p)) |-> ce );

  // Basic functional covers
  cover property ( ce && $past(ce) );
  cover property ( ce ##[1:10] ce );                 // CE with gap
  cover property ( ce && (a==0 || b==0) );           // multiply by zero
  cover property ( ce && a==S_MIN );                 // min operand
  cover property ( ce && a==S_MAX );
  cover property ( ce && b==S_MIN );
  cover property ( ce && b==S_MAX );
  cover property ( ce && (a[W-1] ^ b[W-1]) );        // neg*pos
  cover property ( ce && (!a[W-1] && !b[W-1]) );     // pos*pos
  cover property ( ce && (a[W-1] && b[W-1]) );       // neg*neg
  cover property ( $rose(!reset) ##[1:5] ce );       // first CE after reset

endmodule

bind fir_mul_32s_32s_3bkb_MulnS_0 fir_mul_32s_32s_3bkb_MulnS_0_sva sva_i();