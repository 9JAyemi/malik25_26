// SVA checker for my_flip_flop
module my_flip_flop_sva (
  input logic clk,
  input logic d,
  input logic rst,
  input logic q
);

  // Synchronous reset forces q to 0 on the next clock (and never X)
  a_rst_forces_zero: assert property (@(posedge clk)
    rst |=> (q === 1'b0)
  );

  // When not in reset and past d is known, q reflects previous d
  a_capture_d: assert property (@(posedge clk)
    (!rst && !$isunknown($past(d))) |=> (q == $past(d))
  );

  // q changes only on clk rising edge (no glitches)
  a_q_only_changes_on_clk: assert property (@(posedge q or negedge q)
    $rose(clk)
  );

  // Coverage
  c_reset_seen:  cover property (@(posedge clk) rst ##1 (q === 1'b0));
  c_cap_one:     cover property (@(posedge clk) (!rst && d==1'b1) ##1 (q==1'b1));
  c_cap_zero:    cover property (@(posedge clk) (!rst && d==1'b0) ##1 (q==1'b0));
  c_q_rose:      cover property (@(posedge q) 1);
  c_q_fell:      cover property (@(negedge q) 1);

endmodule

// Optional bind
bind my_flip_flop my_flip_flop_sva u_my_flip_flop_sva (.clk(clk), .d(d), .rst(rst), .q(q));