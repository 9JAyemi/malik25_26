// SVA for barrel_shifter_4bit
// Bind this module; it checks 1-cycle functional latency, output stability, X-safety, and full op coverage.

module barrel_shifter_4bit_sva #(parameter W=4)
(
  input logic              clk,
  input logic [W-1:0]      in,
  input logic [1:0]        shift,
  input logic [W-1:0]      out
);

  function automatic logic [W-1:0] exp_out(input logic [W-1:0] d, input logic [1:0] s);
    unique case (s)
      2'b00: exp_out = d << 1;                         // logical left by 1
      2'b01: exp_out = d >> 1;                         // logical right by 1
      2'b10: exp_out = {d[1:0], d[W-1:2]};             // rotate left by 2 (for W=4)
      2'b11: exp_out = {d[W-1], d[W-1:1]};             // arithmetic right by 1 (sign extend)
      default: exp_out = 'x;
    endcase
  endfunction

  // Functional correctness with 1-cycle latency
  property p_func_1cycle;
    @(posedge clk)
      !$isunknown({$past(in), $past(shift)}) |-> out == exp_out($past(in), $past(shift));
  endproperty
  assert property (p_func_1cycle);

  // Out changes only at posedge clk
  property p_out_only_at_posedge;
    @(negedge clk) $stable(out) until_with posedge clk;
  endproperty
  assert property (p_out_only_at_posedge);

  // No X on out after update; inputs known when sampled
  assert property (@(posedge clk) !$isunknown(out));
  assert property (@(posedge clk) !$isunknown(shift));

  // Functional covers (ensure all modes/data paths are exercised)
  cover property (@(posedge clk) shift==2'b00 && out == $past(in << 1));
  cover property (@(posedge clk) shift==2'b01 && out == $past(in >> 1));
  cover property (@(posedge clk) shift==2'b10 && out == $past({in[1:0], in[3:2]}));
  cover property (@(posedge clk) shift==2'b11 && out == $past({in[3], in[3:1]}));

  // Edge-case stimulus coverage
  cover property (@(posedge clk) shift==2'b00 && $past(in)==4'h0);
  cover property (@(posedge clk) shift==2'b00 && $past(in)==4'hF);
  cover property (@(posedge clk) shift==2'b01 && $past(in)==4'h8);
  cover property (@(posedge clk) shift==2'b11 && $past(in[3])==1'b1); // sign-extend case

endmodule

bind barrel_shifter_4bit barrel_shifter_4bit_sva i_barrel_shifter_4bit_sva (.clk(clk), .in(in), .shift(shift), .out(out));