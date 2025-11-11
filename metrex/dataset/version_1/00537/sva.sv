// SVA for d_flip_flop_nand and top_module
// Focus: correctness, X-propagation, and concise coverage

// Assertions bound into each d_flip_flop_nand instance
module dff_nand_sva (input clk, d, q, input n_clk, n_d, n_q);

  default clocking cb @ (posedge clk or negedge clk or posedge d or negedge d); endclocking

  // Functional truth: q == (~d) | clk (avoids preponed sampling via ##0)
  a_func:        assert property (cb 1'b1 |-> ##0 (q === ((~d) | clk)))
                   else $error("%m: q != (~d)|clk");

  // Internal nets must match intended logic
  a_inv_wires:   assert property (cb 1'b1 |-> ##0 (n_clk === ~clk && n_d === ~d))
                   else $error("%m: n_clk/n_d mismatch");
  a_gate1:       assert property (cb 1'b1 |-> ##0 (n_q === ~(n_d & n_clk)))
                   else $error("%m: gate1 NAND mismatch");
  a_gate2:       assert property (cb 1'b1 |-> ##0 (q   === ~(n_q & n_clk)))
                   else $error("%m: gate2 NAND mismatch");

  // Mode-specific simplifications
  a_clk_hi_q1:   assert property (cb clk  |-> ##0 (q === 1'b1))
                   else $error("%m: clk=1 must force q=1");
  a_clk_lo_qnd:  assert property (cb !clk |-> ##0 (q === ~d))
                   else $error("%m: clk=0 must make q=~d");

  // X-safety: if inputs are known, output must be known
  a_no_x:        assert property (cb (!$isunknown({clk,d})) |-> ##0 (!$isunknown(q)))
                   else $error("%m: Known inputs produced X/Z on q");

  // Lightweight coverage: exercise both d values under both clk phases and q toggles
  c_clk_pos_d0:  cover property (@(posedge clk) d==1'b0);
  c_clk_pos_d1:  cover property (@(posedge clk) d==1'b1);
  c_clk_neg_d0:  cover property (@(negedge clk) d==1'b0);
  c_clk_neg_d1:  cover property (@(negedge clk) d==1'b1);
  c_q_rose:      cover property (@(posedge d or negedge d or posedge clk or negedge clk) $rose(q));
  c_q_fell:      cover property (@(posedge d or negedge d or posedge clk or negedge clk) $fell(q));

endmodule

bind d_flip_flop_nand dff_nand_sva dff_nand_sva_i (.*);

// Top-level array/bus-oriented checks and coverage
module top_sva (input clk, input [7:0] d, input [7:0] q, input [7:0] q_temp);

  default clocking cb @ (posedge clk or negedge clk); endclocking

  // Structural connection check
  a_bus_connect: assert property (cb 1'b1 |-> ##0 (q === q_temp))
                    else $error("%m: q != q_temp");

  // For each bit: same functional truth and X-safety (guarded by known inputs)
  genvar i;
  generate
    for (i=0; i<8; i++) begin : GEN_SVA
      a_func_bit: assert property (cb 1'b1 |-> ##0 (q[i] === ((~d[i]) | clk)))
                     else $error("%m: bit%0d q != (~d)|clk", i);
      a_no_x_bit: assert property (cb (!$isunknown({clk,d[i]})) |-> ##0 (!$isunknown(q[i])))
                     else $error("%m: bit%0d Known inputs produced X/Z on q", i);

      // Minimal toggle coverage per bit
      c_rose_bit: cover property (@(posedge q[i]) 1);
      c_fell_bit: cover property (@(negedge q[i]) 1);
    end
  endgenerate

endmodule

bind top_module top_sva top_sva_i (.*);