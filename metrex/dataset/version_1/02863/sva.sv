// SVA for johnson_counter_and_barrel_shifter
// Bind into DUT scope to access internals
module johnson_counter_and_barrel_shifter_sva;

  default clocking @(posedge clk); endclocking

  bit past_valid, past_valid2;
  initial begin past_valid = 0; past_valid2 = 0; end
  always @(posedge clk) begin
    past_valid  <= 1'b1;
    past_valid2 <= past_valid;
  end

  function automatic [3:0] johnson_next(input [3:0] c);
    case (c)
      4'b0001: johnson_next = 4'b0011;
      4'b0011: johnson_next = 4'b0111;
      4'b0111: johnson_next = 4'b1110;
      4'b1110: johnson_next = 4'b1100;
      4'b1100: johnson_next = 4'b1000;
      4'b1000: johnson_next = 4'b0001;
      default: johnson_next = c; // hold on any other value
    endcase
  endfunction

  function automatic [3:0] shift_map(input [3:0] c, input [1:0] s);
    case (s)
      2'b01: shift_map = {c[2], c[1], c[0], c[3]}; // right rotate
      2'b10: shift_map = {c[0], c[3], c[2], c[1]}; // left rotate
      default: shift_map = c;                      // 00 or 11: no shift
    endcase
  endfunction

  // Functional correctness
  a_counter:        assert property (disable iff (!past_valid)
                                     counter == johnson_next($past(counter)));

  a_shifted:        assert property (disable iff (!past_valid)
                                     shifted_counter == shift_map($past(counter), $past(SHIFT)));

  a_Q_pipeline:     assert property (disable iff (!past_valid)
                                     Q == $past(shifted_counter));

  a_Q_2cycle_map:   assert property (disable iff (!past_valid2)
                                     Q == shift_map($past(counter,2), $past(SHIFT,2)));

  a_and_relationship: assert property (disable iff (!past_valid)
                                       and_output == (Q & $past(DATA_IN)));

  // Coverage
  cover_johnson_cycle: cover property (counter==4'b0001 ##1 counter==4'b0011 ##1 counter==4'b0111
                                       ##1 counter==4'b1110 ##1 counter==4'b1100 ##1 counter==4'b1000 ##1 counter==4'b0001);

  cover_shift_right: cover property (past_valid && SHIFT==2'b01);
  cover_shift_left:  cover property (past_valid && SHIFT==2'b10);
  cover_shift_hold:  cover property (past_valid && (SHIFT inside {2'b00,2'b11}));

endmodule

bind johnson_counter_and_barrel_shifter johnson_counter_and_barrel_shifter_sva sva_inst();