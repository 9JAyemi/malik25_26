// SVA checker for mux4to1
// Bind this to the DUT:  bind mux4to1 mux4to1_sva u_mux4to1_sva(.*);

module mux4to1_sva (
  input logic in0, in1, in2, in3,
  input logic sel0, sel1,
  input logic out,
  input logic VPWR, VGND, VPB, VNB
);

  // Optional power-good check (assumes well ties = rails)
  wire pgood = (VPWR === 1'b1) && (VGND === 1'b0) && (VPB === VPWR) && (VNB === VGND);

  // Functional equivalence when controls/data are known
  always_comb begin
    if (pgood && !$isunknown({sel1,sel0,in0,in1,in2,in3})) begin
      assert ( out == ( (sel1 & ((sel0 & in0) | (~sel0 & in1)))
                      | (~sel1 & ((sel0 & in2) | (~sel0 & in3))) ) )
        else $error("mux4to1 functional mismatch");
    end
  end

  // Truth-table mapping (also guards X on out when selected input is known)
  always_comb begin
    if (pgood && !$isunknown({sel1,sel0})) begin
      if ( sel1 &&  sel0) begin
        if (!$isunknown(in0)) assert (!$isunknown(out));
        assert (out == in0);
      end
      if ( sel1 && !sel0) begin
        if (!$isunknown(in1)) assert (!$isunknown(out));
        assert (out == in1);
      end
      if (!sel1 &&  sel0) begin
        if (!$isunknown(in2)) assert (!$isunknown(out));
        assert (out == in2);
      end
      if (!sel1 && !sel0) begin
        if (!$isunknown(in3)) assert (!$isunknown(out));
        assert (out == in3);
      end
    end
  end

  // Degenerate case: all inputs equal and known => out must match regardless of selects
  always_comb begin
    if (pgood && !$isunknown({in0,in1,in2,in3}) && (in0==in1) && (in1==in2) && (in2==in3))
      assert (out == in0) else $error("unanimous-input rule violated");
  end

  // Simple functional coverage

  // Selections exercised
  cover ( sel1 &&  sel0); // select in0
  cover ( sel1 && !sel0); // select in1
  cover (!sel1 &&  sel0); // select in2
  cover (!sel1 && !sel0); // select in3

  // Output values
  cover (out == 1'b0);
  cover (out == 1'b1);

  // Observe each data path when selected (toggle at input propagates to out)
  cover property (@(posedge in0 or negedge in0) pgood &&  sel1 &&  sel0 && (out == in0));
  cover property (@(posedge in1 or negedge in1) pgood &&  sel1 && !sel0 && (out == in1));
  cover property (@(posedge in2 or negedge in2) pgood && !sel1 &&  sel0 && (out == in2));
  cover property (@(posedge in3 or negedge in3) pgood && !sel1 && !sel0 && (out == in3));

  // Selection transitions seen
  cover property (@(posedge sel0 or negedge sel0 or posedge sel1 or negedge sel1)
                  pgood && $changed({sel1,sel0}));

endmodule