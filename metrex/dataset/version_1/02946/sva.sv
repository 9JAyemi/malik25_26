// SVA for up_counter
module up_counter_sva (
  input logic        clk,
  input logic        reset,
  input logic [2:0]  out
);
  default clocking cb @(posedge clk); endclocking

  // Next-state correctness: reset dominates; otherwise increment by 1 (mod-8)
  assert property (reset |=> (out == 3'd0))
    else $error("up_counter: out must be 0 one cycle after reset=1");

  property p_inc_mod1;
    logic [2:0] prev;
    (!reset, prev = out) |=> (out == (prev + 3'd1));
  endproperty
  assert property (p_inc_mod1)
    else $error("up_counter: out must increment by 1 when reset=0");

  // Coverage: full 0..7..0 count without reset
  cover property (disable iff (reset)
    (out==3'd0) ##1 (out==3'd1) ##1 (out==3'd2) ##1 (out==3'd3) ##
    1 (out==3'd4) ##1 (out==3'd5) ##1 (out==3'd6) ##1 (out==3'd7) ##1 (out==3'd0)
  );

  // Coverage: reset forces zero from a nonzero value
  cover property ( (out != 3'd0) ##1 reset ##1 (out == 3'd0) );

  // Coverage: wrap from 7 to 0 without reset
  cover property ( (!reset && out==3'd7) ##1 (!reset && out==3'd0) );
endmodule

// Bind into the DUT
bind up_counter up_counter_sva u_up_counter_sva(.clk(clk), .reset(reset), .out(out));