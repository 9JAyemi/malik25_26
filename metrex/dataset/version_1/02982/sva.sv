// SystemVerilog Assertions for any_edge_detection_pipeline
// Bind directly into the DUT to see internal regs

module any_edge_detection_pipeline_sva (input logic clk, input logic [7:0] in);

  default clocking cb @(posedge clk); endclocking

  // History valid (need 3 cycles of history)
  logic [2:0] pv;
  initial pv = '0;
  always_ff @(posedge clk) pv <= {pv[1:0], 1'b1};
  default disable iff (!pv[2]);

  // Pipeline integrity
  a_reg1: assert property (reg1 == $past(in));
  a_reg2: assert property (reg2 == $past(reg1));
  a_reg3: assert property (reg3 == $past(reg2));

  // Functional correctness vs input history
  // anyedge == ~reg1 & reg2 & reg3 == ~$past(in,1) & $past(in,2) & $past(in,3)
  a_out_hist: assert property ( anyedge == (~$past(in,1) & $past(in,2) & $past(in,3)) );

  // No X/Z on pipeline regs and output once filled
  a_no_x: assert property ( !$isunknown({reg1, reg2, reg3, anyedge}) );

  // Per-bit: single-cycle pulse and coverage
  genvar i;
  generate
    for (i=0; i<8; i++) begin : G
      a_single_pulse: assert property ( !(anyedge[i] && $past(anyedge[i])) );
      c_bit_seen:     cover  property ( anyedge[i] );
    end
  endgenerate

  // Vector-level coverage: at least one bit fires
  c_any: cover property ( anyedge != 8'h00 );

endmodule

bind any_edge_detection_pipeline any_edge_detection_pipeline_sva sva (.clk(clk), .in(in));