// SVA bind module for GrayCodeStateMachine
module GrayCodeStateMachine_sva #(
  parameter int n = 4,
  parameter int m = 2
)(
  input  logic              clk,
  input  logic              rst,
  input  logic [n-1:0]      in,
  input  logic [m-1:0]      out,
  input  logic [n-1:0]      state_reg,
  input  logic [n-1:0]      state_next
);

  // Static configuration check
  initial begin
    assert (n == 4 && m == 2)
      else $error("GrayCodeStateMachine must be instantiated with n=4, m=2 for these SVA");
  end

  // Helpers (4-bit)
  function automatic logic [3:0] gray_enc4 (input logic [3:0] b);
    return b ^ (b >> 1);
  endfunction

  function automatic logic [3:0] gray2bin4 (input logic [3:0] g);
    logic [3:0] b;
    b[3] = g[3];
    b[2] = b[3] ^ g[2];
    b[1] = b[2] ^ g[1];
    b[0] = b[1] ^ g[0];
    return b;
  endfunction

  // Reconstructed combinational specs
  logic [3:0] in_vec;
  assign in_vec = {in[0], in[1], in[2], in[3]};

  logic [3:0] exp_state_next;
  assign exp_state_next = gray_enc4(in_vec ^ gray2bin4(state_reg[3:0]));

  logic b0, b1, b2, b3;
  assign b0 = state_reg[3] ^~ in[0];
  assign b1 = state_reg[2] ^~ in[1];
  assign b2 = state_reg[1] ^~ in[2];
  assign b3 = state_reg[0] ^~ in[3];

  logic [1:0] exp_out;
  assign exp_out = { (b0 ^ b2), ((b0 ^ b1) ^ b3) };

  // Reset behavior (async reset, checked on clk edge)
  assert property (@(posedge clk) rst |-> (state_reg[3:0] == 4'b0000))
    else $error("state_reg not cleared during reset");

  // Sequential update: state_reg <= state_next
  assert property (@(posedge clk) (!rst && !$past(rst)) |-> (state_reg == $past(state_next)))
    else $error("state_reg did not capture previous state_next");

  // Next-state combinational correctness (matches full case table)
  assert property (@(posedge clk) state_next[3:0] == exp_state_next)
    else $error("state_next mismatch vs expected gray_enc(in ^ gray2bin(state_reg))");

  // Output logic equivalence (compact closed form of the 16-way compare)
  assert property (@(posedge clk) out == exp_out)
    else $error("out mismatch vs expected function of state_reg and in");

  // X-prop hygiene
  assert property (@(posedge clk) (!$isunknown({in, state_reg}))) // recommend constraining drivers
    else $warning("Inputs/state_reg contain X/Z; following checks may be inconclusive");

  assert property (@(posedge clk) (!$isunknown({in, state_reg})) |-> (!$isunknown({state_next, out})))
    else $error("Combinational outputs/state_next contain X/Z with known inputs/state");

  assert property (@(posedge clk) !$isunknown(out))
    else $error("out contains X/Z");

  // Coverage: exercise all states and all output codes
  genvar k;
  generate
    for (k = 0; k < 16; k++) begin : COV_STATES
      cover property (@(posedge clk) disable iff (rst) state_reg[3:0] == k[3:0]);
    end
  endgenerate

  cover property (@(posedge clk) disable iff (rst) out == 2'b00);
  cover property (@(posedge clk) disable iff (rst) out == 2'b01);
  cover property (@(posedge clk) disable iff (rst) out == 2'b10);
  cover property (@(posedge clk) disable iff (rst) out == 2'b11);

endmodule

// Bind into the DUT
bind GrayCodeStateMachine
  GrayCodeStateMachine_sva #(.n(n), .m(m)) u_graycode_sva (
    .clk       (clk),
    .rst       (rst),
    .in        (in),
    .out       (out),
    .state_reg (state_reg),
    .state_next(state_next)
  );