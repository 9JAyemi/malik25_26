// SVA for sky130_fd_sc_ms__clkdlyinv3sd3 (Y = ~A)

module sky130_fd_sc_ms__clkdlyinv3sd3_sva #(parameter bit FATAL=0) (
  input logic A,
  input logic Y
);

  // Combinational invariant (4-state aware, sampled after updates)
  always_comb begin
    assert #0 (Y === ~A)
      else if (FATAL) $fatal(0, "sky130_fd_sc_ms__clkdlyinv3sd3: Y != ~A");
           else       $error   ("sky130_fd_sc_ms__clkdlyinv3sd3: Y != ~A");
  end

  // Edge-to-edge consistency (no spontaneous Y toggles)
  assert property (@(posedge Y) ##0 $fell(A))
    else $error("sky130_fd_sc_ms__clkdlyinv3sd3: Y rose without A falling");
  assert property (@(negedge Y) ##0 $rose(A))
    else $error("sky130_fd_sc_ms__clkdlyinv3sd3: Y fell without A rising");

  // Functional edges
  assert property (@(posedge A) ##0 (Y===1'b0))
    else $error("sky130_fd_sc_ms__clkdlyinv3sd3: Y!=0 on A rising");
  assert property (@(negedge A) ##0 (Y===1'b1))
    else $error("sky130_fd_sc_ms__clkdlyinv3sd3: Y!=1 on A falling");

  // Coverage
  cover property (@(posedge A) ##0 (Y===1'b0));
  cover property (@(negedge A) ##0 (Y===1'b1));
  cover property (@(posedge Y));
  cover property (@(negedge Y));

endmodule

// Bind into DUT
bind sky130_fd_sc_ms__clkdlyinv3sd3 sky130_fd_sc_ms__clkdlyinv3sd3_sva sva_i (.A(A), .Y(Y));