// SVA for gray_counter, barrel_shifter, and_gate, and top integration.
// Concise, high-signal-quality checks plus focused coverage.

module gray_counter_sva (
  input logic       clk,
  input logic       reset,
  input logic       ena,
  input logic [3:0] q
);
  default clocking @(posedge clk); endclocking

  // Synchronous reset
  assert property (reset |=> q == 4'h0)
    else $error("%m: q not zero after reset");

  // Next-state function
  assert property (!reset && ena  |=> q == ($past(q) ^ ($past(q) >> 1)))
    else $error("%m: ena=1 next-state mismatch");
  assert property (!reset && !ena |=> q == ($past(q) ^ ($past(q) << 1)))
    else $error("%m: ena=0 next-state mismatch");

  // No X/Z when active
  assert property (!reset |-> !$isunknown(q))
    else $error("%m: q has X/Z when not in reset");

  // Coverage (exercise both paths and observe any state change)
  cover property ($rose(reset));
  cover property (!reset && ena);
  cover property (!reset && !ena);
  cover property (!reset ##1 $changed(q));
endmodule


module barrel_shifter_sva (
  input logic [3:0] a,
  input logic [1:0] b,
  input logic [3:0] q
);
  // Purely combinational correctness
  always_comb begin
    assert ( q == ( b[1]
                    ? ( b[0] ? {a[1:0], 2'b00}
                             : {2'b00, a[3:2]} )
                    : ( b[0] ? {a[0], a[3:1]}
                             : {a[2:0], a[3]} ) ) )
      else $error("%m: barrel_shifter output mismatch");
  end
endmodule


module and_gate_sva (
  input logic [3:0] a,
  input logic [3:0] q
);
  // Purely combinational correctness and invariants
  always_comb begin
    assert (q == (a & 4'hC))
      else $error("%m: and_gate output mismatch");
    assert (q[1:0] == 2'b00)
      else $error("%m: low bits not masked to 0");
    assert (q[3:2] == a[3:2])
      else $error("%m: high bits not passed through");
  end
endmodule


module top_module_sva (
  input  logic       clk,
  input  logic       reset,
  input  logic       ena,
  input  logic [1:0] select,
  input  logic [3:0] q,
  input  logic [3:0] gray_out,
  input  logic [3:0] shift_out,
  input  logic [3:0] and_out
);
  default clocking @(posedge clk); endclocking

  // Integration correctness and sanitization
  assert property (!reset |-> !$isunknown({gray_out,shift_out,and_out,q}))
    else $error("%m: X/Z detected on datapath when not in reset");

  assert property (q == and_out)
    else $error("%m: top.q != and_out");

  // Output reset behavior
  assert property (reset |=> q == 4'h0)
    else $error("%m: top.q not zero after reset");

  // Constant downstream mask invariant
  assert property (q[1:0] == 2'b00)
    else $error("%m: top.q[1:0] not zero");

  // Functional coverage: select modes and enable paths
  cover property (!reset && select == 2'b00);
  cover property (!reset && select == 2'b01);
  cover property (!reset && select == 2'b10);
  cover property (!reset && select == 2'b11);
  cover property (!reset && ena);
  cover property (!reset && !ena);

  // Optional covers (helpful to detect stuck-at-0 behavior)
  cover property (!reset && (gray_out != 4'h0));
  cover property (!reset && (shift_out[1:0] != 2'b00)); // mask effect visibility
endmodule


// Bind the SVA modules to the DUT
bind gray_counter   gray_counter_sva   gc_sva  (.*);
bind barrel_shifter barrel_shifter_sva bs_sva  (.*);
bind and_gate       and_gate_sva       ag_sva  (.*);
bind top_module     top_module_sva     top_sva (.*);