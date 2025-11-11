// SVA checker for mux4. Bind this to the DUT.
module mux4_sva(
  input logic [3:0] in,
  input logic [1:0] sel,
  input logic       out
);

  // Golden combinational selection
  let sel_bit = (sel==2'b00) ? in[0] :
                (sel==2'b01) ? in[1] :
                (sel==2'b10) ? in[2] :
                                in[3];

  // Functional equivalence (continuous)
  always_comb
    assert (out === sel_bit)
      else $error("mux4: out(%0b) != selected(%0b) sel=%0b in=%0b", out, sel_bit, sel, in);

  // Prevent X/Z select (avoids latch-through behavior of incomplete case)
  always_comb
    assert (!$isunknown(sel))
      else $error("mux4: sel has X/Z: sel=%b", sel);

  // If inputs/sel known, out must be known
  always_comb
    if (!$isunknown({in,sel}))
      assert (!$isunknown(out))
        else $error("mux4: out X/Z with known inputs. sel=%b in=%b out=%b", sel, in, out);

  // No spurious out toggles: every out edge caused by sel change or selected input change
  property out_change_has_cause;
    @(posedge out or negedge out)
      $changed(sel) or $changed(sel_bit);
  endproperty
  assert property (out_change_has_cause);

  // Coverage: each path exercised
  cover property (sel==2'b00 && out === in[0]);
  cover property (sel==2'b01 && out === in[1]);
  cover property (sel==2'b10 && out === in[2]);
  cover property (sel==2'b11 && out === in[3]);

  // Coverage: data toggles propagate when selected
  genvar gi;
  generate
    for (gi=0; gi<4; gi++) begin : cov_each_input_toggles
      localparam int IDX = gi;
      cover property (@(posedge in[IDX] or negedge in[IDX]) (sel==IDX) && out===in[IDX]);
    end
  endgenerate

endmodule

bind mux4 mux4_sva mux4_sva_i (.*);