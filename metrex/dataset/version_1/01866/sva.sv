// SVA for barrel_shifter
module barrel_shifter_sva (
  input logic        clk,
  input logic [3:0]  data,
  input logic [1:0]  shift,
  input logic [3:0]  stage1_out,
  input logic [3:0]  stage2_out,
  input logic [3:0]  q
);

  function automatic logic [3:0] ror4(input logic [3:0] d, input logic [1:0] s);
    case (s)
      2'b00: ror4 = d;
      2'b01: ror4 = {d[0], d[3:1]};
      2'b10: ror4 = {d[1:0], d[3:2]};
      2'b11: ror4 = {d[2:0], d[3]};
    endcase
  endfunction

  logic past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Combinational correctness of stage1
  ap_stage1_func: assert property (@(posedge clk)
    stage1_out == ror4(data, shift))
    else $error("stage1_out != rotate(data,shift)");

  // Pipeline correctness
  ap_stage2_pipe: assert property (@(posedge clk) disable iff (!past_valid)
    stage2_out == $past(stage1_out))
    else $error("stage2_out != $past(stage1_out)");

  ap_q_pipe: assert property (@(posedge clk) disable iff (!past_valid)
    q == $past(stage2_out))
    else $error("q != $past(stage2_out)");

  ap_q_matches_inputs: assert property (@(posedge clk) disable iff (!past_valid)
    q == ror4($past(data), $past(shift)))
    else $error("q != rotate($past(data),$past(shift))");

  // No X/Z on outputs when inputs are known
  ap_no_x: assert property (@(posedge clk)
    !$isunknown({data,shift}) |-> !$isunknown({stage1_out,stage2_out,q}))
    else $error("X/Z on outputs with known inputs");

  // Coverage
  covergroup cg_shift @(posedge clk);
    coverpoint shift { bins s[] = {2'b00,2'b01,2'b10,2'b11}; }
  endgroup
  cg_shift cg = new();

  cp_pipeline_flow: cover property (@(posedge clk)
    past_valid && $changed({data,shift}) ##1
    q == ror4($past(data), $past(shift)));

  cp_wrap1: cover property (@(posedge clk) data==4'b0001 && shift==2'b11);
  cp_wrap2: cover property (@(posedge clk) data==4'b1000 && shift==2'b01);
  cp_wrap3: cover property (@(posedge clk) data==4'b1010 && shift==2'b10);

endmodule

bind barrel_shifter barrel_shifter_sva sva_i (
  .clk(clk),
  .data(data),
  .shift(shift),
  .stage1_out(stage1_out),
  .stage2_out(stage2_out),
  .q(q)
);