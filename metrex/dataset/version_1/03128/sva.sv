// SVA for axis_infrastructure_v1_1_clock_synchronizer
// Bind this file; focuses on correctness, conciseness, and useful coverage.

module axis_infrastructure_v1_1_clock_synchronizer_sva #(
  parameter int C_NUM_STAGES = 4
) (
  input  logic clk,
  input  logic synch_in,
  input  logic synch_out,
  input  logic [(C_NUM_STAGES>0?C_NUM_STAGES:1)-1:0] synch_d
);

  default clocking cb @(posedge clk); endclocking

  generate
    if (C_NUM_STAGES > 0) begin : g_sync

      // Output equals input delayed by N cycles (after N valid samples)
      assert property (disable iff ($initstate)
                       $past(1'b1, C_NUM_STAGES) |-> (synch_out == $past(synch_in, C_NUM_STAGES)));

      // Output is the last stage
      assert property (synch_out === synch_d[C_NUM_STAGES-1]);

      // Stage-by-stage pipeline linkage (including head sampling)
      assert property (disable iff ($initstate) synch_d[0] == $past(synch_in));
      genvar i;
      for (i=1; i<C_NUM_STAGES; i++) begin : g_stage_link
        assert property (disable iff ($initstate) synch_d[i] == $past(synch_d[i-1]));
      end

      // Knownness: when the corresponding input sample was known, output is known
      assert property (disable iff ($initstate)
                       $past(1'b1, C_NUM_STAGES) && !$isunknown($past(synch_in, C_NUM_STAGES))
                       |-> !$isunknown(synch_out));

      // Minimal but meaningful coverage: edge and pulse propagation
      cover property ($rose(synch_in) ##(C_NUM_STAGES) $rose(synch_out));
      cover property ($fell(synch_in) ##(C_NUM_STAGES) $fell(synch_out));
      cover property ($rose(synch_in) ##1 $fell(synch_in)
                      ##(C_NUM_STAGES-1) $rose(synch_out) ##1 $fell(synch_out));

    end else begin : g_bypass

      // Pure bypass when N==0
      assert property (synch_out === synch_in);

      // Coverage for bypass behavior
      cover property ($rose(synch_in) and $rose(synch_out));
      cover property ($fell(synch_in) and $fell(synch_out));

    end
  endgenerate

endmodule

// Bind to the DUT
bind axis_infrastructure_v1_1_clock_synchronizer
  axis_infrastructure_v1_1_clock_synchronizer_sva #(.C_NUM_STAGES(C_NUM_STAGES))
    u_sva (
      .clk      (clk),
      .synch_in (synch_in),
      .synch_out(synch_out),
      .synch_d  (synch_d)
    );