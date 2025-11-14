// SVA checker for rotator_pipeline
// Bind this to the DUT to verify sequential updates and q mapping.
// Focused, high-signal-coverage, concise.

module rotator_pipeline_sva_chk (
  input logic               clk,
  input logic               load,
  input logic [1:0]         ena,
  input logic [99:0]        data,
  input logic [99:0]        q,
  input logic [99:0]        pipeline_reg1,
  input logic [99:0]        pipeline_reg2,
  input logic [99:0]        pipeline_reg3
);

  default clocking cb @(posedge clk); endclocking

  // Basic past-valid and depth tracking
  logic past_valid; initial past_valid = 1'b0;
  always_ff @(posedge clk) past_valid <= 1'b1;

  logic [2:0] past_depth; initial past_depth = '0;
  always_ff @(posedge clk) if (past_depth != 3'd7) past_depth <= past_depth + 3'd1;
  wire past3_ok = (past_depth >= 3'd3);

  // One-cycle sequential semantics
  assert property (disable iff (!past_valid)
    load |=> (pipeline_reg1 == $past(data)) &&
              (pipeline_reg2 == $past(pipeline_reg1)) &&
              (pipeline_reg3 == $past(pipeline_reg2))
  ) else $error("Load-path sequential update failed");

  assert property (disable iff (!past_valid)
    !load |=> (pipeline_reg1 == $past(pipeline_reg3)) &&
               (pipeline_reg2 == $past(pipeline_reg1)) &&
               (pipeline_reg3 == $past(pipeline_reg2))
  ) else $error("Rotate-path sequential update failed");

  // Multi-cycle pipeline under continuous load (depth-3)
  assert property (disable iff (!past3_ok)
    load[*3] |=> (pipeline_reg1 == $past(data,1)) &&
                 (pipeline_reg2 == $past(data,2)) &&
                 (pipeline_reg3 == $past(data,3))
  ) else $error("Continuous-load 3-cycle pipeline alignment failed");

  // Combinational mapping: all ena encodings yield q == pipeline_reg3 in this RTL
  assert property (disable iff (!past_valid)
    q == pipeline_reg3
  ) else $error("q must reflect pipeline_reg3 for all ena encodings");

  // ------------- Coverage -------------
  // Exercise all enable encodings (case arms)
  cover property (ena == 2'b00);
  cover property (ena == 2'b01);
  cover property (ena == 2'b10);
  cover property (ena == 2'b11);

  // Observe single rotate step when !load
  cover property (disable iff (!past_valid)
    !load ##1 {pipeline_reg1,pipeline_reg2,pipeline_reg3} ==
               {$past(pipeline_reg3), $past(pipeline_reg1), $past(pipeline_reg2)}
  );

  // See 3 consecutive loads and no-loads
  cover property (disable iff (!past3_ok) load[*3]);
  cover property (disable iff (!past3_ok) !load[*3]);

  // Ring periodicity over 3 no-load cycles
  cover property (disable iff (!past3_ok)
    !load[*3] ##1 (pipeline_reg1 == $past(pipeline_reg1,3) &&
                   pipeline_reg2 == $past(pipeline_reg2,3) &&
                   pipeline_reg3 == $past(pipeline_reg3,3))
  );

endmodule

// Bind to DUT; connects DUT ports and internal pipeline regs by name
bind rotator_pipeline rotator_pipeline_sva_chk u_rotator_pipeline_sva_chk (.*,
  .pipeline_reg1(pipeline_reg1),
  .pipeline_reg2(pipeline_reg2),
  .pipeline_reg3(pipeline_reg3)
);