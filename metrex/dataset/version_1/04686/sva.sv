// SVA checker for pipelined_vector
module pipelined_vector_sva #(parameter int DEPTH = 3)(
    input logic              clk,
    input logic [2:0]        vec,
    input logic [2:0]        outv,
    input logic              o2, o1, o0,
    // internal pipeline taps
    input logic [2:0]        stage1_out,
    input logic [2:0]        stage2_out,
    input logic [2:0]        stage3_out
);

  // Basic enable after pipeline fills
  bit init_done;
  int unsigned cycles;
  always_ff @(posedge clk) if (!init_done) begin
    cycles <= cycles + 1;
    if (cycles >= DEPTH) init_done <= 1'b1;
  end

  default clocking cb @(posedge clk); endclocking
  default disable iff (!init_done);

  // Combinational tap checks (catch glitches)
  always_comb begin
    assert #0 ({o2,o1,o0} == vec)
      else $error("o[2:0] must mirror vec continuously");
    assert #0 (outv == stage3_out)
      else $error("outv must be a pure tap of stage3_out");
  end

  // Per-stage pipeline correctness
  assert property (stage1_out == $past(vec))
    else $error("stage1_out must capture vec each cycle");
  assert property (stage2_out == $past(stage1_out))
    else $error("stage2_out must capture stage1_out each cycle");
  assert property (stage3_out == $past(stage2_out))
    else $error("stage3_out must capture stage2_out each cycle");

  // End-to-end latency: exact 3-cycle delay
  assert property (outv == $past(vec, DEPTH))
    else $error("outv must equal vec delayed %0d cycles", DEPTH);

  // No early or late update when input changes once then holds
  assert property ($changed(vec) ##1 $stable(vec)[*2]
                   |-> (outv != $past(vec,1))
                       ##1 (outv != $past(vec,2))
                       ##1 (outv == $past(vec,3)))
    else $error("Exact 3-cycle latency violated on single change");

  // No spurious output activity when input held
  assert property ($stable(vec)[*3] |-> $stable(outv))
    else $error("outv must remain stable when vec is stable for 3 cycles");

  // Knownness: if last 3 vec samples are known, outv must be known
  assert property (!$isunknown(vec | $past(vec,1) | $past(vec,2)) |-> !$isunknown(outv))
    else $error("outv must not be X/Z when last 3 vec samples are known");

  // Coverage: observe end-to-end propagation after a change
  cover property ($changed(vec) ##1 $stable(vec)[*2] ##1 (outv == $past(vec,3)));

  // Coverage: all 8 values propagate with correct latency
  genvar v;
  generate
    for (v = 0; v < 8; v++) begin : g_val_cov
      cover property (vec == v ##3 outv == v);
    end
  endgenerate

  // Coverage: stress with consecutive input changes
  cover property ($changed(vec)[*4]);

endmodule

// Bind into DUT (access internal pipeline regs)
bind pipelined_vector pipelined_vector_sva #(.DEPTH(3)) u_pipelined_vector_sva (
  .clk(clk),
  .vec(vec),
  .outv(outv),
  .o2(o2), .o1(o1), .o0(o0),
  .stage1_out(stage1_out),
  .stage2_out(stage2_out),
  .stage3_out(stage3_out)
);