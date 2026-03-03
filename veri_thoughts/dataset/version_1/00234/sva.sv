// SVA for absolute_counter. Bind this to the DUT.
module absolute_counter_sva;

  // Bound into absolute_counter scope; direct access to DUT signals.
  default clocking cb @(posedge clk); endclocking

  // Helper expression for absolute value of input
  let abs32 = in[31] ? -$signed(in) : $signed(in);

  // Combinational functional correctness (continuous checks)
  always_comb begin
    assert (abs_val == abs32)
      else $error("absolute_counter: abs_val mismatch");
    assert (out == ({4'd0, abs32} + {32'd0, counter}))
      else $error("absolute_counter: out mismatch");
    assert (!$isunknown(out)) else $error("absolute_counter: out has X/Z");
  end

  // Synchronous reset: counter clears next cycle
  assert property (rst |=> counter == 4'h0);

  // Increment when en (priority over ld), modulo-16
  assert property (!rst && en |=> counter == ($past(counter)+4'd1)[3:0]);

  // Load when ld and !en
  assert property (!rst && !en && ld |=> counter == $past(load_data));

  // Hold when neither en nor ld
  assert property (!rst && !en && !ld |=> counter == $past(counter));

  // Explicit priority case (en && ld): still increments
  assert property (!rst && en && ld |=> counter == ($past(counter)+4'd1)[3:0]);

  // No X on state after reset deasserted
  assert property (disable iff (rst) !$isunknown(counter));

  // Coverage
  cover property (rst);
  cover property (!rst && en);                        // increment activity
  cover property (!rst && !en && ld);                 // load activity
  cover property (!rst && en && ld);                  // priority case seen
  cover property (!rst && $past(counter)==4'hF && en && counter==4'h0); // wrap-around
  cover property (in[31]);                            // negative input seen
  cover property (!in[31]);                           // non-negative input seen
  cover property (in == 32'h8000_0000);               // INT_MIN corner
endmodule

bind absolute_counter absolute_counter_sva sva_absolute_counter();