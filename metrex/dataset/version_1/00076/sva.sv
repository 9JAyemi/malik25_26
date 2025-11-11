// SystemVerilog Assertions for mux4to1
// Bind into the DUT for check/coverage. Focused, concise, and high quality.

module mux4to1_sva (
  input  logic [3:0] data_in,
  input  logic [1:0] sel,
  input  logic       data_out,
  input  logic [3:0] sel_inv
);

  // Core functional check (deferred immediate to avoid race with combinational logic)
  always_comb begin
    // No X/Z on sel (prevents latchy behavior of the if/else chain)
    assert (!$isunknown(sel))
      else $error("mux4to1: sel has X/Z");

    // Functional mapping when sel is known
    if (!$isunknown(sel)) begin
      assert (#0 (data_out === data_in[sel]))
        else $error("mux4to1: data_out != data_in[sel]");

      // X-propagation: if selected input is X/Z, output must be X/Z; if known, output must be known
      assert (#0 ($isunknown(data_in[sel]) == $isunknown(data_out)))
        else $error("mux4to1: X-propagation mismatch");
    end

    // Internal sel_inv consistency (width-mismatch awareness)
    assert (#0 (sel_inv[1:0] === ~sel))
      else $error("mux4to1: sel_inv[1:0] != ~sel");
    assert (#0 (sel_inv[3:2] === 2'b00))
      else $error("mux4to1: sel_inv[3:2] should be 0 due to width extension");
  end

  // Coverage: observe all select values
  cover property (@(data_in or sel) (!$isunknown(sel) && sel==2'b00));
  cover property (@(data_in or sel) (!$isunknown(sel) && sel==2'b01));
  cover property (@(data_in or sel) (!$isunknown(sel) && sel==2'b10));
  cover property (@(data_in or sel) (!$isunknown(sel) && sel==2'b11));

  // Coverage: when selected input toggles, output follows
  cover property (@(data_in[0]) (!$isunknown(sel) && sel==2'b00 && !$isunknown(data_in[0])) ##0 $changed(data_out));
  cover property (@(data_in[1]) (!$isunknown(sel) && sel==2'b01 && !$isunknown(data_in[1])) ##0 $changed(data_out));
  cover property (@(data_in[2]) (!$isunknown(sel) && sel==2'b10 && !$isunknown(data_in[2])) ##0 $changed(data_out));
  cover property (@(data_in[3]) (!$isunknown(sel) && sel==2'b11 && !$isunknown(data_in[3])) ##0 $changed(data_out));

endmodule

// Bind into all instances of mux4to1 (accesses internal sel_inv)
bind mux4to1 mux4to1_sva u_mux4to1_sva (
  .data_in (data_in),
  .sel     (sel),
  .data_out(data_out),
  .sel_inv (sel_inv)
);