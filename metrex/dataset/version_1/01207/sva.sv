// SVA for macc_simple_arst_clr_ena
module macc_simple_arst_clr_ena_sva (
  input logic        clk,
  input logic        rst,
  input logic        clr,
  input logic        ena,
  input logic [7:0]  A,
  input logic [7:0]  B,
  input logic [15:0] Z
);
  default clocking cb @(posedge clk); endclocking

  // Async reset: immediate and while asserted
  assert property (@(posedge rst) ##0 (Z == 16'd0))
    else $error("Z must clear immediately on posedge rst");
  assert property (@(posedge clk) rst |-> (Z == 16'd0))
    else $error("Z must be 0 while rst is asserted");

  // Hold when not enabled (post-reset cycles)
  assert property (@(posedge clk)
                   (!rst && !$past(rst) && !ena) |-> (Z == $past(Z)))
    else $error("Z changed while ena=0");

  // Enabled behavior: clear vs accumulate (post-reset cycles)
  assert property (@(posedge clk)
                   (!rst && !$past(rst) && ena)
                   |-> (Z == (clr ? (A*B) : ($past(Z) + (A*B)))))
    else $error("Z update mismatch when ena=1");

  // First accumulate right after reset deassert (previous Z=0)
  assert property (@(posedge clk)
                   ($past(rst) && !rst && ena && !clr) |-> (Z == (A*B)))
    else $error("First accumulate after reset should equal A*B");

  // Z changes (post-reset) only when enabled
  assert property (@(posedge clk)
                   (!rst && !$past(rst) && (Z != $past(Z))) |-> ena)
    else $error("Z changed without ena");

  // Basic functional coverage
  cover property (@(posedge clk) (!rst && !$past(rst) && (ena && clr)));
  cover property (@(posedge clk) (!rst && !$past(rst) && (ena && !clr)));
  cover property (@(posedge clk) (!rst && !$past(rst) && !ena));

  // Two-cycle accumulate sequence
  cover property (@(posedge clk)
                  (!rst && !$past(rst) && ena && !clr) ##1 (ena && !clr));

  // Accumulate wraparound (16-bit)
  cover property (@(posedge clk)
                  (!rst && !$past(rst) && ena && !clr &&
                   (($past(Z) + (A*B)) < $past(Z))));
endmodule

// Bind to DUT
bind macc_simple_arst_clr_ena macc_simple_arst_clr_ena_sva sva_i(
  .clk(clk), .rst(rst), .clr(clr), .ena(ena), .A(A), .B(B), .Z(Z)
);