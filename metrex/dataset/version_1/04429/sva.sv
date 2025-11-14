// SVA for integrate
// Bind into DUT for internal signal visibility

module integrate_sva
  #(parameter INPUTW = 16,
    parameter ACCUMW = 32,
    parameter OUTPUTW = 16)
   (input  clk_i,
    input  rst_i,
    input  ena_i,
    input  dump_i,
    input  [INPUTW-1:0]  data_i,
    input  [ACCUMW-1:0]  data_ext,
    input  [ACCUMW-1:0]  accum,
    input  stb_o,
    input  [OUTPUTW-1:0] integ_o);

  // Default clock
  default clocking cb @ (posedge clk_i); endclocking

  // Elaboration-time parameter sanity
  initial begin
    assert (ACCUMW >= INPUTW)
      else $error("ACCUMW(%0d) < INPUTW(%0d)", ACCUMW, INPUTW);
    assert (ACCUMW >= OUTPUTW)
      else $error("ACCUMW(%0d) < OUTPUTW(%0d)", ACCUMW, OUTPUTW);
  end

  // Helper for $past validity
  bit past_valid;
  always_ff @(posedge clk_i) past_valid <= 1'b1;

  // Sign-extension correctness
  assert property (data_ext[INPUTW-1:0] == data_i);
  assert property (data_ext[ACCUMW-1:INPUTW] == {ACCUMW-INPUTW{data_i[INPUTW-1]}});

  // Reset/disable clears outputs and accumulator on the next cycle
  assert property ( (rst_i || !ena_i) |=> (accum == '0 && integ_o == '0) );

  // Accumulate when enabled and no dump
  assert property ( (!rst_i && ena_i && !dump_i)
                    |=> (accum == $past(accum) + $past(data_ext)
                         && integ_o == $past(integ_o)) );

  // Dump behavior: output MSBs of previous accum, reset accum to current data_ext
  assert property ( (!rst_i && ena_i && dump_i)
                    |=> (integ_o == $past(accum)[ACCUMW-1 -: OUTPUTW]
                         && accum   == $past(data_ext)) );

  // Strobe is a 1-cycle delayed dump
  assert property ( past_valid |-> (stb_o == $past(dump_i)) );

  // When strobe is high, integ_o matches the previously dumped value (alignment)
  assert property ( past_valid && stb_o |-> (integ_o == $past(accum)[ACCUMW-1 -: OUTPUTW]) );

  // No unintended integ_o updates (already covered above, but check also across enable transitions)
  assert property ( (!rst_i && ena_i && !dump_i) |=> $stable(integ_o) );

  // ------------- Functional coverage -------------

  // At least two accumulations then a dump
  cover property ( !rst_i && ena_i ##1 (!dump_i && ena_i && !rst_i)[*2:$] ##1 dump_i );

  // Back-to-back dumps
  cover property ( !rst_i && ena_i && dump_i ##1 dump_i );

  // Negative input observed
  cover property ( data_i[INPUTW-1] == 1'b1 );

  // Non-negative input observed
  cover property ( data_i[INPUTW-1] == 1'b0 );

  // Disable then re-enable around activity and dump
  cover property (
    !rst_i && ena_i && !dump_i ##1
    !ena_i ##1
    ena_i ##1
    dump_i
  );

endmodule

// Bind into the DUT
bind integrate integrate_sva #(.INPUTW(INPUTW), .ACCUMW(ACCUMW), .OUTPUTW(OUTPUTW))
  u_integrate_sva (.*);