// SVA for contador_AD_HH_2dig
// Bind example:
// bind contador_AD_HH_2dig contador_AD_HH_2dig_sva sva(.clk(clk), .reset(reset), .en_count(en_count),
//                                                      .enUP(enUP), .enDOWN(enDOWN), .data_HH(data_HH), .q_act(q_act));

module contador_AD_HH_2dig_sva(
  input logic        clk,
  input logic        reset,
  input logic [3:0]  en_count,
  input logic        enUP,
  input logic        enDOWN,
  input logic [7:0]  data_HH,
  input logic [4:0]  q_act
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  function automatic [7:0] bcd8(input logic [4:0] v);
    bcd8 = { (v/10)[3:0], (v%10)[3:0] };
  endfunction

  // Async reset behavior
  a_async_reset: assert property (@(posedge reset) q_act == 5'd0);

  // Legal state space
  a_in_range:    assert property (q_act inside {[5'd0:5'd23]});

  // State changes only when enabled to count
  a_change_allowed: assert property ($changed(q_act) |-> $past(en_count==4'd3 && (enUP || enDOWN)));

  // Increment path (UP has priority over DOWN)
  a_inc: assert property ((en_count==4'd3 && enUP)
                          |=> q_act == (($past(q_act) >= 5'd23) ? 5'd0 : $past(q_act)+5'd1));

  // Decrement path (only when UP is low)
  a_dec: assert property ((en_count==4'd3 && !enUP && enDOWN)
                          |=> q_act == (($past(q_act) == 5'd0) ? 5'd23 : $past(q_act)-5'd1));

  // Hold conditions
  a_hold_not3: assert property ((en_count != 4'd3) |=> q_act == $past(q_act));
  a_hold_idle: assert property ((en_count == 4'd3 && !enUP && !enDOWN) |=> q_act == $past(q_act));

  // UP vs DOWN priority when both asserted
  a_priority: assert property ((en_count==4'd3 && enUP && enDOWN)
                               |=> q_act == (($past(q_act) >= 5'd23) ? 5'd0 : $past(q_act)+5'd1));

  // Output mapping to BCD nibbles
  a_bcd_map: assert property ((q_act inside {[5'd0:5'd23]}) |-> data_HH == bcd8(q_act));
  a_default_map: assert property ((!(q_act inside {[5'd0:5'd23]})) |-> data_HH == 8'h00);

  // Coverage
  genvar v;
  generate
    for (v=0; v<=23; v++) begin : C_STATES
      c_state: cover property (q_act == v[4:0]);
    end
  endgenerate

  c_wrap_up:   cover property ((en_count==4'd3 && enUP   && q_act==5'd23) |=> q_act==5'd0);
  c_wrap_down: cover property ((en_count==4'd3 && !enUP && enDOWN && q_act==5'd0) |=> q_act==5'd23);
  c_hold_not3: cover property ((en_count!=4'd3) |=> q_act==$past(q_act));
  c_both_cmds: cover property (en_count==4'd3 && enUP && enDOWN);

endmodule