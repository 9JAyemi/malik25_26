// SVA for mux_4to1 — concise, high-quality checks and coverage
// Bind this checker to the DUT.

checker mux_4to1_sva (
  input logic        in0, in1, in2, in3,
  input logic [1:0]  sel,
  input logic        out
);

  // Functional equivalence when select is known
  always_comb begin
    if (!$isunknown(sel)) begin
      assert (out === ((sel==2'b00)? in0 :
                       (sel==2'b01)? in1 :
                       (sel==2'b10)? in2 : in3))
        else $error("mux_4to1: out mismatch for sel=%b", sel);
    end
  end

  // No X/Z on out when all drivers and select are known
  always_comb begin
    if (!$isunknown({in0,in1,in2,in3,sel})) begin
      assert (!$isunknown(out))
        else $error("mux_4to1: out is X/Z with fully known inputs/sel");
    end
  end

  // Basic state coverage for all select values
  always_comb begin
    cover (! $isunknown(sel) && sel==2'b00);
    cover (! $isunknown(sel) && sel==2'b01);
    cover (! $isunknown(sel) && sel==2'b10);
    cover (! $isunknown(sel) && sel==2'b11);
  end

  // Propagation coverage: selected input edges drive out
  always @(posedge in0) if (!$isunknown(sel) && sel==2'b00 && !$isunknown(in0)) cover (out==1'b1);
  always @(negedge in0) if (!$isunknown(sel) && sel==2'b00 && !$isunknown(in0)) cover (out==1'b0);

  always @(posedge in1) if (!$isunknown(sel) && sel==2'b01 && !$isunknown(in1)) cover (out==1'b1);
  always @(negedge in1) if (!$isunknown(sel) && sel==2'b01 && !$isunknown(in1)) cover (out==1'b0);

  always @(posedge in2) if (!$isunknown(sel) && sel==2'b10 && !$isunknown(in2)) cover (out==1'b1);
  always @(negedge in2) if (!$isunknown(sel) && sel==2'b10 && !$isunknown(in2)) cover (out==1'b0);

  always @(posedge in3) if (!$isunknown(sel) && sel==2'b11 && !$isunknown(in3)) cover (out==1'b1);
  always @(negedge in3) if (!$isunknown(sel) && sel==2'b11 && !$isunknown(in3)) cover (out==1'b0);

endchecker

bind mux_4to1 mux_4to1_sva sva_i (.*);