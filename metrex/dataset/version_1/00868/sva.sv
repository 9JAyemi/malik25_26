// SVA checker for mux_4to1_case
// Focus: functional equivalence, optional X-checking on select, concise coverage.

module mux_4to1_case_sva #(parameter bit ENA_ASSERT_KNOWN_SEL = 0) (
  input logic a, b, c, d,
  input logic sel0, sel1,
  input logic out
);

  // Optional: forbid X/Z on select
  always_comb if (ENA_ASSERT_KNOWN_SEL) begin
    assert (!$isunknown({sel1,sel0}))
      else $error("mux_4to1_case: sel has X/Z: sel1=%b sel0=%b", sel1, sel0);
  end

  // Core functional check (combinational equivalence)
  always_comb begin
    if (!$isunknown({sel1,sel0})) begin
      assert (out === (sel1 ? (sel0 ? d : c) : (sel0 ? b : a)))
        else $error("mux_4to1_case: out != selected input (sel=%b%b out=%b a=%b b=%b c=%b d=%b)",
                    sel1, sel0, out, a, b, c, d);
    end
  end

  // Minimal yet meaningful coverage
  // 1) Hit all select values
  cover property (@(posedge sel0 or negedge sel0 or posedge sel1 or negedge sel1) {sel1,sel0}==2'b00);
  cover property (@(posedge sel0 or negedge sel0 or posedge sel1 or negedge sel1) {sel1,sel0}==2'b01);
  cover property (@(posedge sel0 or negedge sel0 or posedge sel1 or negedge sel1) {sel1,sel0}==2'b10);
  cover property (@(posedge sel0 or negedge sel0 or posedge sel1 or negedge sel1) {sel1,sel0}==2'b11);

  // 2) Propagation: when selected input toggles, out matches in zero time
  cover property (@(posedge a or negedge a) (!sel1 && !sel0) ##0 (out===a));
  cover property (@(posedge b or negedge b) (!sel1 &&  sel0) ##0 (out===b));
  cover property (@(posedge c or negedge c) ( sel1 && !sel0) ##0 (out===c));
  cover property (@(posedge d or negedge d) ( sel1 &&  sel0) ##0 (out===d));

endmodule

// Bind into the DUT
bind mux_4to1_case mux_4to1_case_sva #(.ENA_ASSERT_KNOWN_SEL(0))
  u_mux_4to1_case_sva (.a(a), .b(b), .c(c), .d(d), .sel0(sel0), .sel1(sel1), .out(out));