// SVA checkers for top_module and submodules (concise, quality-focused)
// Bind these into your DUT; no testbench code required.

// Checker for mux_6to1: functional correctness and coverage
module mux_6to1_sva (
  input [2:0] sel,
  input [5:0] data_in,
  input [3:0] data_out
);
  // Sample on any relevant change
  event ev; always @(sel, data_in, data_out) -> ev;

  // Expected behavior: zero-extended selected bit, default=0 for sel>=6
  let sel_bit = (sel <= 3'd5) ? data_in[sel] : 1'b0;
  let exp_out = {3'b000, sel_bit};

  // If inputs known, output must match expected
  assert property (@(ev) !$isunknown({sel, data_in}) |-> (data_out === exp_out))
    else $error("mux_6to1: data_out mismatch (sel=%0d data_in=%b got=%b exp=%b)",
                sel, data_in, data_out, exp_out);

  // Basic X-prop sanity: known inputs imply known output
  assert property (@(ev) !$isunknown({sel, data_in}) |-> !$isunknown(data_out))
    else $error("mux_6to1: X/Z on output with known inputs");

  // Coverage: each select value, and both output LSB values
  genvar i;
  generate
    for (i=0; i<8; i++) begin : gen_cov_sel
      cover property (@(ev) sel==i[2:0]);
    end
  endgenerate
  cover property (@(ev) sel <= 3'd5 && data_in[sel]==1'b0 && data_out[0]==1'b0);
  cover property (@(ev) sel <= 3'd5 && data_in[sel]==1'b1 && data_out[0]==1'b1);
endmodule

bind mux_6to1 mux_6to1_sva u_mux_6to1_sva(.sel(sel), .data_in(data_in), .data_out(data_out));


// Checker for top_module: end-to-end functionality and coverage
module top_module_sva (
  input [2:0] sel,
  input [5:0] data_in,
  input       in,
  input [3:0] mux_out,
  input       out,
  input [3:0] or_out
);
  // Sample on any relevant change
  event ev; always @(sel, data_in, in, mux_out, out, or_out) -> ev;

  // Top-level expected behavior derived from given RTL
  // mux_out is 000{data_in[5]} when sel<=5, else 0000
  let exp_mux_lsb = (sel <= 3'd5) ? data_in[5] : 1'b0;
  let exp_mux_out = {3'b000, exp_mux_lsb};
  let exp_out     = ~in;
  let exp_or_out  = exp_mux_out | exp_out; // 1-bit exp_out is zero-extended by SV rules

  // Assertions
  assert property (@(ev) mux_out === exp_mux_out)
    else $error("top: mux_out mismatch (sel=%0d data_in[5]=%0b got=%b exp=%b)",
                sel, data_in[5], mux_out, exp_mux_out);

  assert property (@(ev) out === exp_out)
    else $error("top: NOT gate mismatch (in=%0b out=%0b exp=%0b)", in, out, exp_out);

  // Structural equivalence of OR
  assert property (@(ev) or_out === (mux_out | out))
    else $error("top: or_out != (mux_out | out) (mux_out=%b out=%0b or_out=%b)",
                mux_out, out, or_out);

  // Strengthen: full computed expectation for or_out
  assert property (@(ev) or_out === exp_or_out)
    else $error("top: or_out mismatch (got=%b exp=%b)", or_out, exp_or_out);

  // Sanity: upper bits must be zero at both mux_out and or_out
  assert property (@(ev) mux_out[3:1] == 3'b000)
    else $error("top: mux_out[3:1] not zero (%b)", mux_out[3:1]);
  assert property (@(ev) or_out[3:1] == 3'b000)
    else $error("top: or_out[3:1] not zero (%b)", or_out[3:1]);

  // Known inputs imply known outputs
  assert property (@(ev) !$isunknown({sel, data_in, in}) |-> !$isunknown({mux_out, out, or_out}))
    else $error("top: X/Z on outputs with known inputs");

  // Coverage: exercise select space, both NOT gate outputs, and OR outcomes
  genvar j;
  generate
    for (j=0; j<8; j++) begin : gen_cov_top_sel
      cover property (@(ev) sel==j[2:0]);
    end
  endgenerate
  cover property (@(ev) in==0 && out==1);
  cover property (@(ev) in==1 && out==0);

  // OR LSB driven by mux vs NOT gate vs both-zero
  cover property (@(ev) (sel<=3'd5) && (data_in[5]==1) && (in==1) && (or_out[0]==1)); // from mux
  cover property (@(ev) (sel<=3'd5) && (data_in[5]==0) && (in==0) && (or_out[0]==1)); // from NOT
  cover property (@(ev) (sel>=3'd6) && (in==1) && (or_out[0]==0));                    // both zero
  cover property (@(ev) (sel<=3'd5) && (data_in[5]==0) && (in==1) && (or_out[0]==0)); // both zero
endmodule

bind top_module top_module_sva u_top_module_sva(
  .sel(sel), .data_in(data_in), .in(in),
  .mux_out(mux_out), .out(out), .or_out(or_out)
);