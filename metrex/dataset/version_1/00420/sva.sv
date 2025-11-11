// SVA for accu. Bind into the DUT to access internals (stage, acc).
module accu_sva;
  // Reset values must hold while reset is asserted
  assert property (@(posedge clk) (!rst_n) |-> (acc==10'd0 && stage==3'd0 && valid_b==1'b0 && data_out==10'd0));

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  // Basic invariants
  assert property (stage inside {3'd0,3'd1,3'd2,3'd3});
  assert property (ready_a == (stage==3'd0));

  // Stage transitions
  assert property ((stage==3'd0 && valid_a) |=> stage==3'd1);
  assert property ((stage==3'd1 && valid_a) |=> stage==3'd2);
  assert property ((stage==3'd2 && valid_a) |=> stage==3'd3);
  assert property (stage==3'd3 |=> stage==3'd0);

  // Hold behavior when not accepting
  assert property ((stage inside {3'd0,3'd1,3'd2} && !valid_a) |=> (stage==$past(stage) && acc==$past(acc)));
  assert property (stage==3'd3 |=> acc==$past(acc));

  // Accumulator updates (modulo 10 bits)
  property p_acc_load;
    automatic logic [9:0] di;
    (stage==3'd0 && valid_a, di={2'b0,data_in}) |=> acc==di;
  endproperty
  assert property (p_acc_load);

  property p_acc_add;
    automatic logic [9:0] ap, di;
    (stage inside {3'd1,3'd2} && valid_a, ap=acc, di={2'b0,data_in}) |=> acc==((ap+di) & 10'h3FF);
  endproperty
  assert property (p_acc_add);

  // Output/valid_b behavior
  assert property ($changed(data_out) |-> stage==3'd3);
  assert property ($rose(valid_b) |-> (stage==3'd3 && data_out==$past(acc)));
  // valid_b never falls during active operation (sticky until reset)
  assert property (!$fell(valid_b));

  // End-to-end: three accepts produce correct sum at output
  property p_sum3;
    automatic logic [9:0] a0,a1,a2;
    ((stage==3'd0 && valid_a, a0={2'b0,data_in})
     ##[1:$] (stage==3'd1 && valid_a, a1={2'b0,data_in})
     ##[1:$] (stage==3'd2 && valid_a, a2={2'b0,data_in})
     ##1 (stage==3'd3 && $rose(valid_b)))
    |-> (data_out == ((a0 + a1 + a2) & 10'h3FF));
  endproperty
  assert property (p_sum3);

  // Coverage
  cover property ((stage==3'd0 && valid_a) ##1 (stage==3'd1 && valid_a) ##1 (stage==3'd2 && valid_a) ##1 (stage==3'd3 && $rose(valid_b)));
  cover property ((stage==3'd0 && valid_a) ##[2:10] (stage==3'd1 && valid_a) ##[2:10] (stage==3'd2 && valid_a) ##1 (stage==3'd3 && $rose(valid_b)));
endmodule

bind accu accu_sva u_accu_sva();