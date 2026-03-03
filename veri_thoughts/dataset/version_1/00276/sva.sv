// SVA checker for booth_encoder_7_new
module booth_encoder_7_new_sva
(
  input logic        clk,
  input logic        rst_n,      // active-low; tie high if unused
  input logic [2:0]  B_in,
  input logic [2:0]  A_out
);

  default clocking @(posedge clk); endclocking
  default disable iff (!rst_n);

  function automatic logic [2:0] f(input logic [2:0] b);
    f[0] = b[0] ^ b[1];
    f[1] = ~b[2] | (~b[1] & ~b[0]);
    f[2] =  b[2] | (~b[0] &  b[1]);
  endfunction

  // Knownness: clean inputs imply clean outputs
  assert property (!$isunknown(B_in) |-> !$isunknown(A_out));

  // Functional correctness
  assert property (!$isunknown(B_in) |-> (A_out === f(B_in)));

  // Purely combinational behavior at sample points
  assert property ((B_in == $past(B_in)) |-> (A_out == $past(A_out)));
  assert property ((A_out != $past(A_out)) |-> (B_in != $past(B_in)));

  // Independence: A_out[0] depends only on B_in[1:0]
  assert property ($changed(B_in[2]) && $stable(B_in[1:0]) |-> $stable(A_out[0]));

  // Input space coverage (all 8 combinations seen at least once)
  cover property (!$isunknown(B_in) && B_in == 3'b000);
  cover property (!$isunknown(B_in) && B_in == 3'b001);
  cover property (!$isunknown(B_in) && B_in == 3'b010);
  cover property (!$isunknown(B_in) && B_in == 3'b011);
  cover property (!$isunknown(B_in) && B_in == 3'b100);
  cover property (!$isunknown(B_in) && B_in == 3'b101);
  cover property (!$isunknown(B_in) && B_in == 3'b110);
  cover property (!$isunknown(B_in) && B_in == 3'b111);

  // Toggle coverage on each output bit
  cover property ($rose(A_out[0]));  cover property ($fell(A_out[0]));
  cover property ($rose(A_out[1]));  cover property ($fell(A_out[1]));
  cover property ($rose(A_out[2]));  cover property ($fell(A_out[2]));

  // Cover independence scenario observation
  cover property ($changed(B_in[2]) && $stable(B_in[1:0]) && $stable(A_out[0]));

endmodule

// Example bind (adjust clk/rst_n names as appropriate):
// bind booth_encoder_7_new booth_encoder_7_new_sva sva_i (.clk(clk), .rst_n(rst_n), .B_in(B_in), .A_out(A_out));