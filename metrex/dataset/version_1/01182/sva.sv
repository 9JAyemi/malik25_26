// SVA for pipeline_register
// Bindable, concise, and focused on functional correctness and coverage.

module pipeline_register_sva
(
  input logic        clock,
  input logic        clrn,     // active-low, synchronous
  input logic        d,
  input logic        ena,
  input logic        q,
  input logic [2:0]  stage_data
);

  default clocking @(posedge clock); endclocking

  // Controls known (allow data to be X)
  a_ctrl_known: assert property (!$isunknown({clrn, ena}));

  // Combinational binding: q reflects stage_data[0]
  a_q_bind:     assert property (q == stage_data[0]);

  // Reset clears (checked one cycle after reset-sampled edge)
  a_reset: assert property ( $past(clrn)==1'b0 |-> (stage_data==3'b000 && q==1'b0) );

  // Hold when disabled
  a_hold:  assert property ( ($past(clrn)==1'b1 && $past(ena)==1'b0)
                             |-> (stage_data==$past(stage_data) && q==$past(q)) );

  // Shift when enabled
  a_shift: assert property ( ($past(clrn)==1'b1 && $past(ena)==1'b1)
                             |-> ( stage_data[2]==$past(d)
                                   && stage_data[1]==$past(stage_data[2])
                                   && stage_data[0]==$past(stage_data[1]) ) );

  // End-to-end latency: 3 consecutive enabled cycles move d to q
  a_latency3: assert property ( (clrn && ena)[*3] |-> (q == $past(d,2)) );

  // Coverage
  c_reset_pulse: cover property (clrn==1'b0 ##1 clrn==1'b1);
  c_hold:        cover property ( ($past(clrn)==1'b1 && $past(ena)==1'b0)
                                  && stage_data==$past(stage_data) );
  c_shift3:      cover property ( (clrn && ena)[*3] ##0 (q==$past(d,2)) );

endmodule

bind pipeline_register pipeline_register_sva sva_i (.*,.stage_data(stage_data));