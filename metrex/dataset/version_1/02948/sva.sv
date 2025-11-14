// SVA bind for functional_module
bind functional_module functional_module_sva sva_i (.*);

module functional_module_sva (
  input  logic [7:0] dff_out,
  input  logic       xnor_out,
  input  logic [7:0] xor_out
);

  // Core functional check (deferred immediate to avoid races)
  always_comb begin
    assert #0 (xor_out === (dff_out ^ xnor_out))
      else $error("functional_module: xor_out != (dff_out ^ xnor_out). dff_out=%0h xnor_out=%b xor_out=%0h",
                  dff_out, xnor_out, xor_out);

    if (!$isunknown({dff_out, xnor_out}))
      assert #0 (!$isunknown(xor_out))
        else $error("functional_module: xor_out X/Z with known inputs. dff_out=%0h xnor_out=%b xor_out=%0h",
                    dff_out, xnor_out, xor_out);
  end

  // When only xnor_out toggles and dff_out is stable, only LSB changes
  assert property (@(posedge xnor_out or negedge xnor_out)
                     $stable(dff_out)
                   |-> (xor_out[7:1] == dff_out[7:1] && xor_out[0] == ~dff_out[0]));

  // Coverage: exercise both polarities of xnor_out and the expected LSB flip behavior
  cover property (@(posedge xnor_out));
  cover property (@(negedge xnor_out));
  cover property (@(posedge xnor_out or negedge xnor_out)
                    $stable(dff_out) && (xor_out == (dff_out ^ 8'h01)));

  // Coverage: each bit of dff_out toggling propagates to xor_out
  genvar i;
  generate
    for (i = 0; i < 8; i++) begin : g_cov_bit_toggle
      cover property (@(posedge dff_out[i] or negedge dff_out[i])
                        $stable(xnor_out) |-> (xor_out[i] != $past(xor_out[i])));
    end
  endgenerate

endmodule