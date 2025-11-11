// SVA for mux4to1: concise, bindable, clockless (purely combinational)

module mux4to1_sva (
  input logic [3:0] in0, in1, in2, in3,
  input logic       sel0, sel1,
  input logic [3:0] out
);
  wire [1:0] sel = {sel1, sel0};

  // Functional equivalence (golden) — out must equal selected input at all times
  property p_mux_functional;
    out === ((sel==2'b00) ? in0 :
             (sel==2'b01) ? in1 :
             (sel==2'b10) ? in2 :
                            in3);
  endproperty
  assert property (p_mux_functional);

  // No-X propagation when selector and selected input are known
  property p_no_x_when_known;
    (!$isunknown(sel) && !$isunknown(
        (sel==2'b00)? in0 :
        (sel==2'b01)? in1 :
        (sel==2'b10)? in2 : in3))
    |-> (!$isunknown(out));
  endproperty
  assert property (p_no_x_when_known);

  // Per-select strict match (also guards independence from non-selected inputs)
  assert property ( (sel==2'b00) |-> (out === in0) );
  assert property ( (sel==2'b01) |-> (out === in1) );
  assert property ( (sel==2'b10) |-> (out === in2) );
  assert property ( (sel==2'b11) |-> (out === in3) );

  // Functional coverage: hit all select cases and observe correct pass-through
  cover property ( (sel==2'b00) && (out===in0) );
  cover property ( (sel==2'b01) && (out===in1) );
  cover property ( (sel==2'b10) && (out===in2) );
  cover property ( (sel==2'b11) && (out===in3) );

endmodule

// Bind into DUT
bind mux4to1 mux4to1_sva mux4to1_sva_i (
  .in0(in0), .in1(in1), .in2(in2), .in3(in3),
  .sel0(sel0), .sel1(sel1),
  .out(out)
);