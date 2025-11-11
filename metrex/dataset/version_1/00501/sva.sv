// SVA checker for SingleCounter
module SingleCounter_sva (
  input  logic        clock,
  input  logic        reset,
  input  logic        io_input_reset,
  input  logic [5:0]  count,
  input  logic        io_output_done
);

  default clocking cb @(posedge clock); endclocking

  // track past-valid to safely use $past()
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clock) past_valid <= 1'b1;

  // Basic sanity/X checks
  assert property ( !$isunknown({reset, io_input_reset, count, io_output_done}) );
  assert property ( count <= 6'd63 );

  // Reset behavior (synchronous)
  assert property ( (reset || io_input_reset) |-> (count == 6'd0) );
  assert property ( (reset || io_input_reset) |-> !io_output_done );

  // Output equivalence
  assert property ( io_output_done == (count == 6'd63) );

  // State transitions (increment or wrap), guarded by past_valid and no reset in prior cycle
  assert property ( past_valid && $past(!reset && !io_input_reset) && $past(count) != 6'd63
                    |-> count == $past(count) + 6'd1 );

  assert property ( past_valid && $past(!reset && !io_input_reset) && $past(count) == 6'd63
                    |-> count == 6'd0 );

  // No spurious zero without reset or wrap
  assert property ( past_valid && (count == 6'd0) && !$past(reset || io_input_reset)
                    |-> $past(count) == 6'd63 );

  // Done pulse is exactly one cycle wide
  assert property ( io_output_done |=> !io_output_done );

  // Localized step checks around boundary
  assert property ( past_valid && $past(!reset && !io_input_reset) && $past(count) == 6'd62
                    |-> count == 6'd63 && io_output_done );

  assert property ( past_valid && $past(!reset && !io_input_reset) && $past(count) == 6'd63
                    |-> count == 6'd0 && !io_output_done );

  // Coverage
  cover property ( io_output_done );                                        // observe a done pulse
  cover property ( past_valid && $past(count) == 6'd63 && count == 6'd0 );  // observe wrap
  cover property ( $rose(reset) );
  cover property ( $rose(io_input_reset) );
  // One full count period without reset: 0 -> ... -> 63 (done) -> 0
  cover property ( disable iff (reset || io_input_reset)
                   count == 6'd0 ##[1:63] io_output_done ##1 count == 6'd0 );

endmodule

// Bind into the DUT (tool supports bind)
bind SingleCounter SingleCounter_sva u_singlecounter_sva (
  .clock          (clock),
  .reset          (reset),
  .io_input_reset (io_input_reset),
  .count          (count),
  .io_output_done (io_output_done)
);