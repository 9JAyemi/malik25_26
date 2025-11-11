// SVA checker for mux4to1. Bind this to the DUT.
module mux4to1_sva (
  input  logic [3:0] in0,
  input  logic [3:0] in1,
  input  logic [3:0] in2,
  input  logic [3:0] in3,
  input  logic [1:0] sel,
  input  logic [3:0] out
);
  // Functional correctness: when sel is 2-state, out must equal the selected input (including X/Z matching)
  property p_selects_correct_path;
    @(in0 or in1 or in2 or in3 or sel)
      (!$isunknown(sel)) |-> (out === (sel==2'b00 ? in0 :
                                       sel==2'b01 ? in1 :
                                       sel==2'b10 ? in2 : in3));
  endproperty
  assert property (p_selects_correct_path)
    else $error("mux4to1: out != selected input");

  // Output changes must be caused by a sel change or the selected input changing
  property p_out_change_has_cause;
    @(in0 or in1 or in2 or in3 or sel)
      $changed(out) |-> ( $changed(sel)
                       || (sel==2'b00 && $changed(in0))
                       || (sel==2'b01 && $changed(in1))
                       || (sel==2'b10 && $changed(in2))
                       || (sel==2'b11 && $changed(in3)) );
  endproperty
  assert property (p_out_change_has_cause)
    else $error("mux4to1: out changed without a valid cause");

  // Optional sanity: flag any X/Z on sel (helps avoid latch-like simulation behavior)
  assert property (@(in0 or in1 or in2 or in3 or sel) !$isunknown(sel))
    else $warning("mux4to1: sel contains X/Z");

  // Coverage: each select path exercised and produces the corresponding output
  cover property (@(in0 or in1 or in2 or in3 or sel) sel==2'b00 && out===in0);
  cover property (@(in0 or in1 or in2 or in3 or sel) sel==2'b01 && out===in1);
  cover property (@(in0 or in1 or in2 or in3 or sel) sel==2'b10 && out===in2);
  cover property (@(in0 or in1 or in2 or in3 or sel) sel==2'b11 && out===in3);

  // Coverage: observe at least one output change event
  cover property (@(in0 or in1 or in2 or in3 or sel) $changed(out));
endmodule

bind mux4to1 mux4to1_sva u_mux4to1_sva (
  .in0(in0), .in1(in1), .in2(in2), .in3(in3), .sel(sel), .out(out)
);