// SVA for reverse_bit_order_pipeline
// Bind into each instance of the DUT

module reverse_bit_order_pipeline_sva;

  // Access DUT signals hierarchically via bind scope
  // clk, reset, in, out, in_reg, out_reg, out_pipeline_reg

  function automatic [7:0] bitrev8(input [7:0] d);
    bitrev8 = {d[0],d[1],d[2],d[3],d[4],d[5],d[6],d[7]};
  endfunction

  // Reset behavior: synchronous clear observed next cycle
  ap_reset_clears: assert property (@(posedge clk)
    reset |=> (in_reg==8'h00 && out_reg==8'h00 && out_pipeline_reg==8'h00 && out==8'h00))
  else $error("Reset did not clear pipeline to 0s");

  // Stage-to-stage timing and functionality
  ap_in_reg_capture: assert property (@(posedge clk) disable iff (reset)
    in_reg == $past(in,1,reset))
  else $error("in_reg did not capture in (1-cycle)");

  ap_out_reg_reverse: assert property (@(posedge clk) disable iff (reset)
    out_reg == bitrev8($past(in_reg,1,reset)))
  else $error("out_reg not bit-reverse of prior in_reg");

  ap_out_pipe_stage: assert property (@(posedge clk) disable iff (reset)
    out_pipeline_reg == $past(out_reg,1,reset))
  else $error("out_pipeline_reg did not capture prior out_reg");

  ap_out_assign: assert property (@(posedge clk)
    out == out_pipeline_reg)
  else $error("out not equal to out_pipeline_reg");

  // End-to-end: 2-cycle latency, bit-reversed output
  ap_end_to_end: assert property (@(posedge clk) disable iff (reset)
    out == bitrev8($past(in,2,reset)))
  else $error("End-to-end mismatch: out != bitrev(in,2) latency");

  // X-propagation guard: if input known 2 cycles ago, output must be known now
  ap_no_x_out_if_in_known: assert property (@(posedge clk) disable iff (reset)
    !$isunknown($past(in,2,reset)) |-> !$isunknown(out))
  else $error("Unknown on out despite known input history");

  // Functional coverage
  cp_latency_when_input_changes: cover property (@(posedge clk) disable iff (reset)
    $changed(in) ##2 (out == bitrev8($past(in,2,reset))));

  cp_rev_01_to_80: cover property (@(posedge clk) disable iff (reset)
    in==8'h01 ##2 out==8'h80);

  cp_rev_AA_to_55: cover property (@(posedge clk) disable iff (reset)
    in==8'hAA ##2 out==8'h55);

endmodule

bind reverse_bit_order_pipeline reverse_bit_order_pipeline_sva sva_rev_bo_pipeline();