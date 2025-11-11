// SystemVerilog Assertions for rotator
// Focused, concise, high-quality checks with essential coverage

module rotator_sva;
  // Bind into rotator; access DUT signals hierarchically
  // Width derived from DUT
  localparam int W = $bits(q);

  default clocking cb @(posedge clk); endclocking

  // Make $past() safe from time 0
  logic past_valid;
  initial past_valid = 1'b0;
  always @(cb) past_valid <= 1'b1;

  // Helpers
  function automatic [W-1:0] rotR1(input [W-1:0] x);
    rotR1 = {x[0], x[W-1:1]};
  endfunction
  function automatic [W-1:0] rotL1(input [W-1:0] x);
    rotL1 = {x[W-2:0], x[W-1]};
  endfunction

  // Combinational mirror of q
  assert property (q == pipeline_reg[0]);

  // Pipeline shift invariants (hold every cycle)
  assert property (disable iff (!past_valid) pipeline_reg[1] == $past(pipeline_reg[0]));
  assert property (disable iff (!past_valid) pipeline_reg[2] == $past(pipeline_reg[1]));

  // Load behavior dominates rotation
  assert property (disable iff (!past_valid) load |=> q == $past(data));

  // Rotation behaviors (use pipeline_reg[2] of previous cycle)
  // Right rotate by 1 when ena==01
  assert property (disable iff (!past_valid)
    !load && (ena == 2'b01) |=> q == rotR1($past(pipeline_reg[2]))
  );

  // Left rotate by 1 when ena==10
  assert property (disable iff (!past_valid)
    !load && (ena == 2'b10) |=> q == rotL1($past(pipeline_reg[2]))
  );

  // Pass-through when ena is neither 01 nor 10 (i.e., 00 or 11)
  assert property (disable iff (!past_valid)
    !load && !(ena inside {2'b01,2'b10}) |=> q == $past(pipeline_reg[2])
  );

  // shifted_out updates only on rotate and reflects source bit from pipeline_reg[2]
  assert property (disable iff (!past_valid)
    !load && (ena == 2'b01) |=> shifted_out == $past(pipeline_reg[2][0])
  );
  assert property (disable iff (!past_valid)
    !load && (ena == 2'b10) |=> shifted_out == $past(pipeline_reg[2][W-1])
  );
  assert property (disable iff (!past_valid)
    !load && !(ena inside {2'b01,2'b10}) |=> $stable(shifted_out)
  );

  // Minimal but meaningful coverage
  cover property (disable iff (!past_valid) load);
  cover property (disable iff (!past_valid) !load && (ena == 2'b01));
  cover property (disable iff (!past_valid) !load && (ena == 2'b10));
  cover property (disable iff (!past_valid) !load && (ena inside {2'b00,2'b11}));
  cover property (disable iff (!past_valid)
    !load && (ena == 2'b01) ##1 !load && (ena == 2'b10)
  );
endmodule

// Bind into the DUT
bind rotator rotator_sva sva_rotator();