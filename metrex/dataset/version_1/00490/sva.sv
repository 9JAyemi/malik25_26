// SVA checker for decoder; bind this to the DUT.
// Assumes an external sampling clock and active-low reset.
module decoder_sva #(parameter int W_IN=3, W_OUT=8) (
  input  logic                   clk,
  input  logic                   rst_n,
  input  logic [W_IN-1:0]        in,
  input  logic [W_OUT-1:0]       out
);

  typedef logic [W_OUT-1:0] out_t;

  default clocking cb @(posedge clk); endclocking

  // Golden decode function
  function automatic out_t enc(input logic [W_IN-1:0] i);
    enc = out_t'(1) << i;
  endfunction

  // Functional correctness: exact one-hot mapping for all known inputs
  property p_decode_correct;
    disable iff (!rst_n)
      !$isunknown(in) |-> (out == enc(in));
  endproperty
  assert property (p_decode_correct);

  // One-hot guarantee for all known inputs
  property p_onehot_out;
    disable iff (!rst_n)
      !$isunknown(in) |-> $onehot(out);
  endproperty
  assert property (p_onehot_out);

  // No X/Z on output when input is known
  property p_out_known_when_in_known;
    disable iff (!rst_n)
      !$isunknown(in) |-> !$isunknown(out);
  endproperty
  assert property (p_out_known_when_in_known);

  // Combinational stability: if input is stable, output remains stable
  property p_stable_when_in_stable;
    disable iff (!rst_n)
      (!$isunknown(in) && $stable(in)) |-> $stable(out);
  endproperty
  assert property (p_stable_when_in_stable);

  // Functional coverage: hit every input and corresponding output
  genvar i;
  generate
    for (i = 0; i < (1<<W_IN); i++) begin : COV_EACH_INPUT
      cover property (disable iff (!rst_n)
        (in == i) && (out == enc(i)));
    end
  endgenerate

  // Output coverage: see each one-hot output at least once
  genvar j;
  generate
    for (j = 0; j < W_OUT; j++) begin : COV_EACH_OUTPUT
      cover property (disable iff (!rst_n)
        out == (out_t'(1) << j));
    end
  endgenerate

endmodule

// Example bind (edit clk/rst paths to your environment):
// bind decoder decoder_sva u_decoder_sva ( .clk(clk), .rst_n(rst_n), .in(in), .out(out) );