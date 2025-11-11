// SVA for mux_8to1
module mux_8to1_sva (
  input [3:0] sel,
  input [7:0] a, b, c, d,
  input [7:0] mux_out
);

  // Functional correctness (allow delta-cycle for combinational settle)
  assert property (@(a or b or c or d or sel)
                   1 |-> ##0
                   mux_out == (sel[1] ? (sel[0] ? d : c) : (sel[0] ? b : a)))
    else $error("mux_8to1: functional mismatch sel=%0h a=%0h b=%0h c=%0h d=%0h out=%0h",
                sel,a,b,c,d,mux_out);

  // Upper select bits must not affect output when others stable
  assert property (@(sel or a or b or c or d)
                   ($changed(sel[3:2]) && !$changed(sel[1:0]) &&
                    $stable(a) && $stable(b) && $stable(c) && $stable(d))
                   |-> ##0 $stable(mux_out))
    else $error("mux_8to1: out changed due to sel[3:2] only");

  // No X/Z on output when selected input and sel[1:0] are known
  assert property (@(a or b or c or d or sel)
                   (!$isunknown(sel[1:0]) &&
                    ((sel[1:0]==2'b00 && !$isunknown(a)) ||
                     (sel[1:0]==2'b01 && !$isunknown(b)) ||
                     (sel[1:0]==2'b10 && !$isunknown(c)) ||
                     (sel[1:0]==2'b11 && !$isunknown(d))))
                   |-> ##0 !$isunknown(mux_out))
    else $error("mux_8to1: X/Z on mux_out with known select/data");

  // Output must equal one of the inputs (redundant safety net)
  assert property (@(a or b or c or d or sel)
                   1 |-> ##0 (mux_out==a || mux_out==b || mux_out==c || mux_out==d))
    else $error("mux_8to1: out not equal to any input");

  // Coverage: hit all 16 select values
  generate
    genvar i;
    for (i=0; i<16; i++) begin : g_sel_cov
      cover property (@(sel) sel == 4'(i));
    end
  endgenerate

  // Coverage: exercise redundancy of sel[3:2] and all four data legs
  cover property (@(sel) $changed(sel[3:2]) && $stable(sel[1:0]));
  cover property (@(sel or a) (sel[1:0]==2'b00) ##0 (mux_out==a));
  cover property (@(sel or b) (sel[1:0]==2'b01) ##0 (mux_out==b));
  cover property (@(sel or c) (sel[1:0]==2'b10) ##0 (mux_out==c));
  cover property (@(sel or d) (sel[1:0]==2'b11) ##0 (mux_out==d));

endmodule

bind mux_8to1 mux_8to1_sva mux_8to1_sva_i (.*);