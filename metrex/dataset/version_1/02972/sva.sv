// SVA for mux2 – concise, high-quality checks and coverage
// Bind into DUT: bind mux2 mux2_sva i_mux2_sva(.clk(clk), .sel(sel), .in1(in1), .in2(in2), .out(out));

module mux2_sva(input logic clk, sel, in1, in2, out);

  default clocking cb @(posedge clk); endclocking

  logic past_valid;
  initial past_valid = 1'b0;
  always @(cb) past_valid <= 1'b1;

  // Functional correctness: out equals selected input from previous cycle
  assert property (disable iff (!past_valid)
                   out == $past(sel ? in2 : in1))
    else $error("mux2: out != selected input (1-cycle latency)");


  // No spurious output changes if selection and selected input are stable
  assert property (disable iff (!past_valid)
                   (!$changed(sel) &&
                    ((sel==1'b0 && !$changed(in1)) ||
                     (sel==1'b1 && !$changed(in2))))
                   |-> !$changed(out))
    else $error("mux2: out changed without change in sel/selected input");


  // No X/Z on out when previous-cycle inputs/sel were known
  assert property (disable iff (!past_valid)
                   !$isunknown({$past(sel), $past(in1), $past(in2)}) |-> !$isunknown(out))
    else $error("mux2: out is X/Z while inputs/sel were known");


  // Coverage: exercise both data paths and sel activity
  cover property (past_valid && $past(sel)==1'b0 && out == $past(in1));
  cover property (past_valid && $past(sel)==1'b1 && out == $past(in2));
  cover property (past_valid && $changed(sel));

  // Coverage: observe actual output update from each path
  cover property (past_valid && $past(sel)==1'b0 &&
                  $past(in1) != $past(out) && out == $past(in1));
  cover property (past_valid && $past(sel)==1'b1 &&
                  $past(in2) != $past(out) && out == $past(in2));

endmodule