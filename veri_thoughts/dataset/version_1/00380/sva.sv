// SVA for mux_8to1: concise, high-quality checks and coverage
// Bind into DUT: bind mux_8to1 mux_8to1_sva u_mux_8to1_sva(.*);

module mux_8to1_sva (
  input  [3:0] in0, in1, in2, in3, in4, in5, in6, in7,
  input  [2:0] sel,
  input  [3:0] out
);

  // Functional correctness: out equals the selected input (evaluate after delta to avoid races)
  assert property (@(*)) (sel==3'b000) |-> ##0 (out===in0);
  assert property (@(*)) (sel==3'b001) |-> ##0 (out===in1);
  assert property (@(*)) (sel==3'b010) |-> ##0 (out===in2);
  assert property (@(*)) (sel==3'b011) |-> ##0 (out===in3);
  assert property (@(*)) (sel==3'b100) |-> ##0 (out===in4);
  assert property (@(*)) (sel==3'b101) |-> ##0 (out===in5);
  assert property (@(*)) (sel==3'b110) |-> ##0 (out===in6);
  assert property (@(*)) (sel==3'b111) |-> ##0 (out===in7);

  // Out updates correctly on sel change (only when sel resolves to a known value)
  assert property (@(*))
    ($changed(sel) && (sel inside {3'b000,3'b001,3'b010,3'b011,3'b100,3'b101,3'b110,3'b111}))
      |-> ##0 (out === (sel==3'b000 ? in0 :
                        sel==3'b001 ? in1 :
                        sel==3'b010 ? in2 :
                        sel==3'b011 ? in3 :
                        sel==3'b100 ? in4 :
                        sel==3'b101 ? in5 :
                        sel==3'b110 ? in6 : in7));

  // Independence: unselected input changes must not affect out
  assert property (@(*)) (sel!=3'b000 && $changed(in0)) |-> ##0 $stable(out);
  assert property (@(*)) (sel!=3'b001 && $changed(in1)) |-> ##0 $stable(out);
  assert property (@(*)) (sel!=3'b010 && $changed(in2)) |-> ##0 $stable(out);
  assert property (@(*)) (sel!=3'b011 && $changed(in3)) |-> ##0 $stable(out);
  assert property (@(*)) (sel!=3'b100 && $changed(in4)) |-> ##0 $stable(out);
  assert property (@(*)) (sel!=3'b101 && $changed(in5)) |-> ##0 $stable(out);
  assert property (@(*)) (sel!=3'b110 && $changed(in6)) |-> ##0 $stable(out);
  assert property (@(*)) (sel!=3'b111 && $changed(in7)) |-> ##0 $stable(out);

  // Tracking: when selected input changes, out follows after delta
  assert property (@(*)) (sel==3'b000 && $changed(in0)) |-> ##0 (out===in0);
  assert property (@(*)) (sel==3'b001 && $changed(in1)) |-> ##0 (out===in1);
  assert property (@(*)) (sel==3'b010 && $changed(in2)) |-> ##0 (out===in2);
  assert property (@(*)) (sel==3'b011 && $changed(in3)) |-> ##0 (out===in3);
  assert property (@(*)) (sel==3'b100 && $changed(in4)) |-> ##0 (out===in4);
  assert property (@(*)) (sel==3'b101 && $changed(in5)) |-> ##0 (out===in5);
  assert property (@(*)) (sel==3'b110 && $changed(in6)) |-> ##0 (out===in6);
  assert property (@(*)) (sel==3'b111 && $changed(in7)) |-> ##0 (out===in7);

  // Functional coverage: all select values hit
  cover property (@(*)) (sel==3'b000);
  cover property (@(*)) (sel==3'b001);
  cover property (@(*)) (sel==3'b010);
  cover property (@(*)) (sel==3'b011);
  cover property (@(*)) (sel==3'b100);
  cover property (@(*)) (sel==3'b101);
  cover property (@(*)) (sel==3'b110);
  cover property (@(*)) (sel==3'b111);

  // Coverage: selected input toggles and out responds
  cover property (@(*)) (sel==3'b000 && $changed(in0)) |-> ##0 $changed(out);
  cover property (@(*)) (sel==3'b001 && $changed(in1)) |-> ##0 $changed(out);
  cover property (@(*)) (sel==3'b010 && $changed(in2)) |-> ##0 $changed(out);
  cover property (@(*)) (sel==3'b011 && $changed(in3)) |-> ##0 $changed(out);
  cover property (@(*)) (sel==3'b100 && $changed(in4)) |-> ##0 $changed(out);
  cover property (@(*)) (sel==3'b101 && $changed(in5)) |-> ##0 $changed(out);
  cover property (@(*)) (sel==3'b110 && $changed(in6)) |-> ##0 $changed(out);
  cover property (@(*)) (sel==3'b111 && $changed(in7)) |-> ##0 $changed(out);

endmodule

bind mux_8to1 mux_8to1_sva u_mux_8to1_sva (.*);