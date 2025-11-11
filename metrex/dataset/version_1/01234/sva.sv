// SVA for shift_register_ring_counter
module shift_register_ring_counter_sva
(
  input logic       clk,
  input logic       d,
  input logic       q,
  input logic [2:0] shift_reg
);

  // Track $past validity
  logic pv1, pv2, pv3;
  initial {pv1,pv2,pv3} = '0;
  always @(posedge clk) begin
    pv1 <= 1'b1;
    pv2 <= pv1;
    pv3 <= pv2;
  end

  // Correct next-state update on each posedge
  assert property (@(posedge clk)
    pv1 |=> (shift_reg == { $past(shift_reg[1:0]), $past(d) })
  );

  // Combinational mapping to output
  assert property (@(posedge clk)
    q == shift_reg[2]
  );

  // 3-cycle pipeline from d to MSB/q
  assert property (@(posedge clk)
    pv3 |-> (shift_reg[2] == $past(d,3) && q == $past(d,3))
  );

  // Coverage: observe 1 and 0 propagation through the 3-stage delay to q
  cover property (@(posedge clk) $rose(d) ##3 q);
  cover property (@(posedge clk) $fell(d) ##3 !q);

endmodule

// Bind SVA to the DUT (connect internal shift_reg)
bind shift_register_ring_counter shift_register_ring_counter_sva u_sva (.*,.shift_reg(shift_reg));