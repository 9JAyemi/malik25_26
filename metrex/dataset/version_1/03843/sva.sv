// SVA checker for top_module + internal decoder/adder-subtractor
// Requires a sampling clock 'clk' visible in bind scope.

module top_module_sva (
  input logic        clk,
  // top_module ports
  input logic [1:0]  in,
  input logic [3:0]  a,
  input logic [3:0]  b,
  input logic        sub,
  input logic [3:0]  q,
  input logic        overflow,
  // internal nets
  input logic [3:0]  dec_out,
  input logic [3:0]  addsub_out,
  input logic        addsub_overflow
);
  default clocking @(posedge clk); endclocking

  // Decoder: exact mapping and one-hot
  assert property (dec_out == (4'b0001 << in));
  assert property ($onehot(dec_out));

  // Adder-subtractor: exact 5-bit arithmetic
  assert property ({addsub_overflow, addsub_out} ==
                   (sub ? ({1'b0,a} - {1'b0,b}) : ({1'b0,a} + {1'b0,b})));

  // Top-level gating
  assert property (q == ((in != 2'b00) ? addsub_out : 4'b0));
  assert property (overflow == ((in != 2'b00) ? addsub_overflow : 1'b0));

  // Coverage
  cover property (in == 2'b00);
  cover property (in == 2'b01);
  cover property (in == 2'b10);
  cover property (in == 2'b11);

  cover property (!sub);
  cover property ( sub);

  cover property (!sub && addsub_overflow);
  cover property ( sub && addsub_overflow);

  cover property (in == 2'b00 && q == 4'b0 && overflow == 1'b0);
  cover property (in != 2'b00 && q == addsub_out);
  cover property (in != 2'b00 && overflow == addsub_overflow);
endmodule

// Bind into the DUT (clk must be in scope where you bind)
bind top_module top_module_sva u_top_module_sva (
  .clk               (clk),
  .in                (in),
  .a                 (a),
  .b                 (b),
  .sub               (sub),
  .q                 (q),
  .overflow          (overflow),
  .dec_out           (dec_out),
  .addsub_out        (addsub_out),
  .addsub_overflow   (addsub_overflow)
);