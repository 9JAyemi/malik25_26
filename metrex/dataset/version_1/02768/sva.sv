// SVA for final_output
module final_output_sva (
  input logic        clk,
  input logic        reset,
  input logic [7:0]  in,
  input logic [7:0]  anyedge,
  input logic [7:0]  count,
  input logic [7:0]  result,
  input logic [7:0]  sr
);

  default clocking cb @(posedge clk); endclocking

  // Reset behavior
  assert property (reset |-> sr == 8'h00);

  // Shift register update (as coded: serial-in from in[0], shift right)
  assert property (!reset && !$past(reset) |-> sr == { $past(in[0]), $past(sr[7:1]) });

  // Bit-wise check of sr shift
  genvar i;
  generate
    for (i=0; i<7; i++) begin : g_sr_bits
      assert property (!reset && !$past(reset) |-> sr[i] == $past(sr[i+1]));
    end
  endgenerate
  assert property (!reset && !$past(reset) |-> sr[7] == $past(in[0]));

  // No X/Z on outputs when inputs are known
  assert property (!reset && !$isunknown({in,sr}) |-> !$isunknown({anyedge,count,result}));

  // Combinational correctness
  assert property (anyedge == (in ^ sr));
  assert property (count   == $countones(in));

  // result = count + rotate_right(anyedge,1), modulo 256
  logic [7:0] rot;
  assign rot = {anyedge[0], anyedge[7:1]};
  assert property (result == (count + rot));

  // -------------- Coverage --------------
  cover property ($fell(reset));
  cover property (!reset && anyedge == 8'h00);
  cover property (!reset && $onehot(anyedge));
  cover property (!reset && count == 8'd0);
  cover property (!reset && count == 8'd8);
  cover property (!reset && (count != 0 || rot != 0) && ((result < count) || (result < rot)));
  cover property (!reset && in[0] ##1 sr[7]);

endmodule

bind final_output final_output_sva sva_inst (.*);