// SVA for seven_segment. Bind this to the DUT.
// Focus: pipeline latency checks, decode correctness, stability, and coverage.

module seven_segment_sva (
  input logic        clk,
  input logic [3:0]  data_in,
  input logic [6:0]  seg_out,
  input logic [3:0]  stage1_out,
  input logic [3:0]  stage2_out,
  input logic [3:0]  stage3_out
);

  // Golden decode function (matches DUT)
  function automatic logic [6:0] exp_seg (input logic [3:0] v);
    case (v)
      4'h0: exp_seg = 7'b1111110;
      4'h1: exp_seg = 7'b0110000;
      4'h2: exp_seg = 7'b1101101;
      4'h3: exp_seg = 7'b1111001;
      4'h4: exp_seg = 7'b0110011;
      4'h5: exp_seg = 7'b1011011;
      4'h6: exp_seg = 7'b1011111;
      4'h7: exp_seg = 7'b1110000;
      4'h8: exp_seg = 7'b1111111;
      4'h9: exp_seg = 7'b1111011;
      default: exp_seg = 7'b0000000;
    endcase
  endfunction

  // Pipeline stage-to-stage latency checks
  a_s1: assert property (@(posedge clk)
           !$isunknown($past(data_in)) |-> stage1_out == $past(data_in))
        else $error("stage1_out != data_in delayed 1");

  a_s2: assert property (@(posedge clk)
           !$isunknown($past(stage1_out)) |-> stage2_out == $past(stage1_out))
        else $error("stage2_out != stage1_out delayed 1");

  a_s3: assert property (@(posedge clk)
           !$isunknown($past(stage2_out)) |-> stage3_out == $past(stage2_out))
        else $error("stage3_out != stage2_out delayed 1");

  a_d3: assert property (@(posedge clk)
           !$isunknown($past(data_in,3)) |-> stage3_out == $past(data_in,3))
        else $error("stage3_out != data_in delayed 3");

  // Combinational decode correctness (for all values, including X/Z -> default)
  a_map_now: assert property (@(posedge clk)
                 seg_out == exp_seg(stage3_out))
             else $error("seg_out mismatches decode(stage3_out)");

  // End-to-end correctness: output matches decode of input after 3 cycles
  a_e2e: assert property (@(posedge clk)
            !$isunknown($past(data_in,3)) |-> seg_out == exp_seg($past(data_in,3)))
        else $error("seg_out != decode(data_in) after 3 cycles");

  // Stability: if stage3_out holds constant across cycles, seg_out must as well
  a_stable: assert property (@(posedge clk)
               $stable(stage3_out) |=> $stable(seg_out))
            else $error("seg_out changed while stage3_out was stable");

  // No X on output when driving value is known
  a_no_x_out: assert property (@(posedge clk)
                    !$isunknown(stage3_out) |-> !$isunknown(seg_out))
              else $error("seg_out has X/Z while stage3_out is known");

  // Coverage: all decimal digits propagate and decode correctly after 3 cycles
  genvar d;
  generate
    for (d = 0; d < 10; d++) begin : cov_digits
      cover property (@(posedge clk)
        data_in == d ##3 (stage3_out == d && seg_out == exp_seg(d)));
    end
  endgenerate

  // Coverage: at least one invalid value propagates to default pattern
  c_invalid: cover property (@(posedge clk)
                  data_in inside {[4'd10:4'd15]} ##3 seg_out == 7'b0000000);

endmodule

// Bind into DUT (connects to internal pipeline registers)
bind seven_segment seven_segment_sva sva (
  .clk(clk),
  .data_in(data_in),
  .seg_out(seg_out),
  .stage1_out(stage1_out),
  .stage2_out(stage2_out),
  .stage3_out(stage3_out)
);