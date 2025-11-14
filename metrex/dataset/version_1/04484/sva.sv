// SVA for top_module and its behavior. Bind this to the DUT.
// Focused, high-quality checks and targeted coverage.

module top_module_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic        select,
  input  logic [3:0]  a,
  input  logic [3:0]  b,
  input  logic [3:0]  c,
  input  logic [3:0]  d,
  input  logic [3:0]  out
);

  // Helpers use the same 4-bit arithmetic semantics as the RTL
  function automatic logic [3:0] f_diff(logic sel, logic [3:0] c_i, logic [3:0] d_i);
    f_diff = sel ? (d_i - c_i) : (c_i - d_i);
  endfunction

  function automatic logic [3:0] f_mux(logic sel, logic [3:0] b_i, logic [3:0] c_i);
    f_mux = sel ? b_i : c_i;
  endfunction

  function automatic logic [3:0] exp_out(logic sel, logic [3:0] a_i, logic [3:0] b_i,
                                         logic [3:0] c_i, logic [3:0] d_i);
    exp_out = f_mux(sel,b_i,c_i) + f_diff(sel,c_i,d_i);
  endfunction

  function automatic bit add_overflow(logic [3:0] x, logic [3:0] y);
    logic [4:0] s; s = x + y; return s[4];
  endfunction

  // No X/Z on key signals
  assert property (@(posedge clk) !$isunknown({select,a,b,c,d,out}))
    else $error("X/Z detected on inputs/outputs");

  // Golden functional equivalence (covers both muxes and diff)
  assert property (@(posedge clk) out == exp_out(select,a,b,c,d))
    else $error("Functional mismatch: out=%0h exp=%0h", out, exp_out(select,a,b,c,d));

  // Out must not change if inputs are stable
  assert property (@(posedge clk) (!$changed({select,a,b,c,d})) |-> !$changed(out))
    else $error("Out changed without input change");

  // Out is independent of 'a' (a is never used in the effective datapath)
  assert property (@(posedge clk) $changed(a) && $stable({select,b,c,d}) |-> $stable(out))
    else $error("'a' should not affect out");

  // 'b' should not affect out when select==0
  assert property (@(posedge clk) !select && $changed(b) && $stable({a,c,d}) |-> $stable(out))
    else $error("'b' should not affect out when select==0");

  // Targeted coverage

  // Exercise both select paths and toggles
  cover property (@(posedge clk) !select);
  cover property (@(posedge clk)  select);
  cover property (@(posedge clk) !select ##1 select);
  cover property (@(posedge clk)  select ##1 !select);

  // Hit key datapath results
  cover property (@(posedge clk) out == 4'h0);
  cover property (@(posedge clk) out == 4'hF);

  // Exercise diff edge cases (no-borrow and wrap/borrow)
  cover property (@(posedge clk) f_diff(select,c,d) == 4'h0);
  cover property (@(posedge clk) f_diff(select,c,d) == 4'hF);

  // Exercise adder overflow (carry-out on 4-bit add)
  cover property (@(posedge clk) add_overflow(f_mux(select,b,c), f_diff(select,c,d)));

  // Explicit path coverage (helps debug which side fired)
  cover property (@(posedge clk)  select && (out == (b + (d - c))));
  cover property (@(posedge clk) !select && (out == (c + (c - d))));

endmodule

bind top_module top_module_sva u_top_module_sva (.*)