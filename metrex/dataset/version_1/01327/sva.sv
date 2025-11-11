// SVA checker for zbroji
// Tie clk/rst_n from your TB; if no reset, tie rst_n=1'b1.
module zbroji_sva (
  input logic        clk,
  input logic        rst_n,
  input logic        ap_start,
  input logic        ap_done,
  input logic        ap_idle,
  input logic        ap_ready,
  input logic [31:0] a,
  input logic [31:0] b,
  input logic [31:0] ap_return
);

  // Outputs follow combinational spec
  assert property (@(posedge clk) disable iff (!rst_n)
    (ap_done == ap_start) && (ap_ready == ap_start) && (ap_idle == 1'b1)
  );

  // 32-bit wrap-around sum
  assert property (@(posedge clk) disable iff (!rst_n)
    ap_return == (a + b)[31:0]
  );

  // Known outputs whenever inputs are known
  assert property (@(posedge clk) disable iff (!rst_n)
    (!$isunknown({ap_start, a, b})) |-> !$isunknown({ap_done, ap_ready, ap_idle, ap_return})
  );

  // Basic functional coverage
  cover property (@(posedge clk) ap_start);
  cover property (@(posedge clk) !ap_start);
  // Addition overflow (carry-out)
  cover property (@(posedge clk) ({1'b0,a} + {1'b0,b})[32]);
  // Zero result (e.g., wrap or 0+0)
  cover property (@(posedge clk) ap_return == 32'd0);

endmodule

// Bind example (adjust clk/rst_n to your TB signals)
// bind zbroji zbroji_sva u_zbroji_sva ( .clk(tb_clk), .rst_n(tb_rst_n),
//   .ap_start(ap_start), .ap_done(ap_done), .ap_idle(ap_idle), .ap_ready(ap_ready),
//   .a(a), .b(b), .ap_return(ap_return));