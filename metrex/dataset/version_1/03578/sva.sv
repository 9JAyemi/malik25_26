// SVA for binary_gray_comparator
module binary_gray_comparator_sva (
  input  logic [3:0] binary_in,
  input  logic [3:0] comp_in_1,
  input  logic [3:0] comp_in_2,
  input  logic [3:0] gray_out,
  input  logic       comp_out,
  input  logic [3:0] shift_out
);

  // Use a combinational event to clock assertions
  event comb_ev;
  always @* -> comb_ev;

  // Sanity: no X/Z on inputs/outputs
  assert property (@(comb_ev) !$isunknown({binary_in, comp_in_1, comp_in_2}))
    else $error("Inputs contain X/Z");
  assert property (@(comb_ev) !$isunknown({gray_out, comp_out, shift_out}))
    else $error("Outputs contain X/Z");

  // Binary to Gray mapping
  assert property (@(comb_ev)
    gray_out == { (binary_in[2]^binary_in[3]),
                  (binary_in[1]^binary_in[2]),
                  (binary_in[0]^binary_in[1]),
                   binary_in[0] })
    else $error("Gray encoding mismatch");

  // Comparator implements unsigned >=
  assert property (@(comb_ev) comp_out == (comp_in_1 >= comp_in_2))
    else $error("Comparator mismatch (expected >=)");

  // Shift function correct (zero-fill)
  assert property (@(comb_ev) shift_out == (comp_out ? (gray_out << 1) : (gray_out >> 1)))
    else $error("Shift operation mismatch");

  // Direction-specific implications (redundant but pinpoint errors)
  assert property (@(comb_ev) comp_out |-> (shift_out == (gray_out << 1)))
    else $error("Left shift expected when comp_out==1");
  assert property (@(comb_ev) !comp_out |-> (shift_out == (gray_out >> 1)))
    else $error("Right shift expected when comp_out==0");

  // Coverage
  cover property (@(comb_ev) comp_out==1);
  cover property (@(comb_ev) comp_out==0);
  cover property (@(comb_ev) (comp_in_1 == comp_in_2) && comp_out);        // equality path
  cover property (@(comb_ev) (comp_in_1 >  comp_in_2) && comp_out);        // greater path
  cover property (@(comb_ev) (comp_in_1 <  comp_in_2) && !comp_out);       // less path
  cover property (@(comb_ev) binary_in == 4'h0);
  cover property (@(comb_ev) binary_in == 4'hF);
  cover property (@(comb_ev) comp_out && (shift_out == (gray_out << 1)));
  cover property (@(comb_ev) !comp_out && (shift_out == (gray_out >> 1)));

endmodule

// Bind into DUT
bind binary_gray_comparator binary_gray_comparator_sva sva_i (
  .binary_in(binary_in),
  .comp_in_1(comp_in_1),
  .comp_in_2(comp_in_2),
  .gray_out(gray_out),
  .comp_out(comp_out),
  .shift_out(shift_out)
);