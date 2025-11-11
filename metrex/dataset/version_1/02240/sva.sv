// SVA for mux_4to1
module mux_4to1_sva (
  input logic [7:0] d0, d1, d2, d3,
  input logic       s0, s1,
  input logic [7:0] out
);

  // Helper
  function automatic logic [7:0] expected(input logic [1:0] sel,
                                          input logic [7:0] d0, d1, d2, d3);
    case (sel)
      2'b00: expected = d0;
      2'b01: expected = d1;
      2'b10: expected = d2;
      2'b11: expected = d3;
      default: expected = {8{1'bx}}; // unknown select
    endcase
  endfunction

  wire [1:0] sel = {s1,s0};

  // Functional correctness when select is known
  property p_mux_correct;
    @(d0 or d1 or d2 or d3 or s0 or s1)
      (!$isunknown(sel)) |-> ##0 (out === expected(sel,d0,d1,d2,d3));
  endproperty
  assert property (p_mux_correct)
    else $error("mux_4to1: out != selected data");

  // No spurious output changes (out changes only due to sel or selected di)
  property p_out_change_has_cause;
    @(d0 or d1 or d2 or d3 or s0 or s1)
      ##0 $changed(out) |-> (
           $changed(s0) || $changed(s1) ||
           (sel==2'b00 && $changed(d0)) ||
           (sel==2'b01 && $changed(d1)) ||
           (sel==2'b10 && $changed(d2)) ||
           (sel==2'b11 && $changed(d3))
         );
  endproperty
  assert property (p_out_change_has_cause)
    else $error("mux_4to1: out changed without cause");

  // If select and selected data are known, out must be known (no X/Z)
  property p_no_x_when_known;
    @(d0 or d1 or d2 or d3 or s0 or s1)
      (!$isunknown(sel) &&
       !$isunknown(expected(sel,d0,d1,d2,d3))) |-> ##0 (!$isunknown(out));
  endproperty
  assert property (p_no_x_when_known)
    else $error("mux_4to1: X/Z on out with known inputs");

  // Coverage: exercise each select value and path, and dynamic behavior
  cover property (@(d0 or d1 or d2 or d3 or s0 or s1) (sel==2'b00) ##0 (out===d0));
  cover property (@(d0 or d1 or d2 or d3 or s0 or s1) (sel==2'b01) ##0 (out===d1));
  cover property (@(d0 or d1 or d2 or d3 or s0 or s1) (sel==2'b10) ##0 (out===d2));
  cover property (@(d0 or d1 or d2 or d3 or s0 or s1) (sel==2'b11) ##0 (out===d3));

  cover property (@(d0 or s0 or s1) (sel==2'b00 && $changed(d0)) ##0 ($changed(out) && out===d0));
  cover property (@(d1 or s0 or s1) (sel==2'b01 && $changed(d1)) ##0 ($changed(out) && out===d1));
  cover property (@(d2 or s0 or s1) (sel==2'b10 && $changed(d2)) ##0 ($changed(out) && out===d2));
  cover property (@(d3 or s0 or s1) (sel==2'b11 && $changed(d3)) ##0 ($changed(out) && out===d3));

  cover property (@(s0 or s1) $changed({s1,s0}) ##0 (out===expected(sel,d0,d1,d2,d3)));

endmodule

// Bind example (instantiate once per DUT instance)
// bind mux_4to1 mux_4to1_sva u_mux_4to1_sva(.d0(d0),.d1(d1),.d2(d2),.d3(d3),.s0(s0),.s1(s1),.out(out));