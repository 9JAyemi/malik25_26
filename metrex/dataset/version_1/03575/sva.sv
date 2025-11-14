// SVA checker for gray_code. Bind this to the DUT.
// bind gray_code gray_code_sva u_gray_code_sva(.in(in), .out(out));

module gray_code_sva (input logic [3:0] in, input logic [3:0] out);

  // Gray mapping: g = b ^ (b >> 1)
  property p_gray_map;
    @(in) !$isunknown(in) |-> ##0 (out == (in ^ {1'b0, in[3:1]}));
  endproperty
  assert property (p_gray_map);

  // No X/Zs on output when inputs are known
  property p_no_x_out;
    @(in) !$isunknown(in) |-> ##0 !$isunknown(out);
  endproperty
  assert property (p_no_x_out);

  // Invertibility: gray -> binary == in
  function automatic logic [3:0] gray2bin (input logic [3:0] g);
    logic [3:0] b;
    b[3]=g[3];
    b[2]=b[3]^g[2];
    b[1]=b[2]^g[1];
    b[0]=b[1]^g[0];
    return b;
  endfunction
  property p_invertible;
    @(in) !$isunknown(in) |-> ##0 (gray2bin(out) == in);
  endproperty
  assert property (p_invertible);

  // Adjacency (coverage): +1/-1 binary step -> one-bit change in Gray
  property p_adjacent_onehot;
    @(in) ##0 (!$isunknown(in) && !$isunknown($past(in))) &&
          ((in == $past(in)+1) || (in == $past(in)-1))
          |-> $onehot(out ^ $past(out));
  endproperty
  cover property (p_adjacent_onehot);

  // Cover all 16 input codes and expected outputs
  genvar i;
  for (i=0; i<16; i++) begin : CODES
    localparam logic [3:0] BIN = logic'(i[3:0]);
    localparam logic [3:0] GR  = BIN ^ {1'b0, BIN[3:1]};
    cover property (@(in) (in==BIN) ##0 (out==GR));
  end

endmodule