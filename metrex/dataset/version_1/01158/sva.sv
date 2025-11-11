// SVA for mux_2to1: concise, high-quality checks and coverage.
// Bind these assertions to the DUT.

module mux_2to1_sva (
  input logic in0,
  input logic in1,
  input logic sel,
  input logic out
);

  // Functional correctness (when sel is known)
  assert property (@(in0 or in1 or sel)
    !$isunknown(sel) |-> (out === (sel ? in1 : in0))
  );

  // No X on out when all inputs are known
  assert property (@(in0 or in1 or sel)
    !$isunknown({in0,in1,sel}) |-> !$isunknown(out)
  );

  // Independence from inactive input (no glitch from non-selected input)
  assert property (@(in1)
    (sel===1'b0 && $stable(sel) && $stable(in0)) |-> $stable(out)
  );
  assert property (@(in0)
    (sel===1'b1 && $stable(sel) && $stable(in1)) |-> $stable(out)
  );

  // Out only changes due to sel or the selected input (when signals are known)
  assert property (@(out)
    !$isunknown({sel,in0,in1}) && $changed(out)
    |-> ($changed(sel) || (sel ? $changed(in1) : $changed(in0)))
  );

  // Coverage: exercise both paths and propagate values
  cover property (@(sel) sel==1'b0 ##1 sel==1'b1);
  cover property (@(in0) sel==1'b0 && $stable(sel) ##0 (out===in0));
  cover property (@(in1) sel==1'b1 && $stable(sel) ##0 (out===in1));

endmodule

bind mux_2to1 mux_2to1_sva sva_i (.in0(in0), .in1(in1), .sel(sel), .out(out));