// SVA for priority_encoder_shift_register
// Bind these into the DUT

module priority_encoder_shift_register_sva;

  // Access DUT scope via bind; no ports needed
  // Helper: expected binary from 3-bit Gray
  function automatic [2:0] gray2bin(input [2:0] g);
    case (g)
      3'b000: gray2bin = 3'b000;
      3'b001: gray2bin = 3'b001;
      3'b010: gray2bin = 3'b011;
      3'b011: gray2bin = 3'b010;
      3'b100: gray2bin = 3'b110;
      3'b101: gray2bin = 3'b111;
      3'b110: gray2bin = 3'b101;
      3'b111: gray2bin = 3'b100;
    endcase
  endfunction

  // Async reset checks (not disabled during reset)
  assert property (@(posedge areset) shift_reg == 4'b0);
  assert property (@(posedge clk) areset |-> shift_reg == 4'b0);

  default clocking cb @(posedge clk); endclocking
  default disable iff (areset);

  // Shift register behavior and priority
  assert property (load |=> shift_reg == $past(in[3:0]));
  assert property (load && ena |=> shift_reg == $past(in[3:0])); // load wins
  assert property (!load && ena |=> shift_reg == {$past(shift_reg[2:0]), $past(shift_reg[3])});
  assert property (!load && !ena |=> shift_reg == $past(shift_reg));

  // 4-cycle rotate returns to original when only ena active
  assert property ((ena && !load)[*4] |=> shift_reg == $past(shift_reg,4));

  // Mux correctness
  assert property (load |-> mux_out == in[3:0]);
  assert property (!load |-> mux_out == shift_reg);

  // Gray-to-decimal correctness
  assert property (decimal_code == gray2bin(in_gray[2:0]));

  // Adder and output correctness
  assert property (sum == ({1'b0, decimal_code} + mux_out));
  assert property (out == sum);

  // No X/Z on key state/outputs (during active operation)
  assert property (!$isunknown(shift_reg));
  assert property (!$isunknown(decimal_code));
  assert property (!$isunknown(sum));
  assert property (!$isunknown(out));

  // Functional coverage (concise but meaningful)
  cover property (@(posedge areset) 1);                           // see reset
  cover property (load && !ena);                                   // pure load
  cover property (!load && ena);                                   // pure rotate
  cover property (load && ena);                                    // load priority over ena
  cover property (!load && !ena);                                  // hold
  cover property ((ena && !load)[*4] ##1 shift_reg == $past(shift_reg,4)); // rotation wrap

  // Cover all 8 Gray codes seen and correctly converted
  cover property (in_gray[2:0]==3'b000 && decimal_code==3'b000);
  cover property (in_gray[2:0]==3'b001 && decimal_code==3'b001);
  cover property (in_gray[2:0]==3'b010 && decimal_code==3'b011);
  cover property (in_gray[2:0]==3'b011 && decimal_code==3'b010);
  cover property (in_gray[2:0]==3'b100 && decimal_code==3'b110);
  cover property (in_gray[2:0]==3'b101 && decimal_code==3'b111);
  cover property (in_gray[2:0]==3'b110 && decimal_code==3'b101);
  cover property (in_gray[2:0]==3'b111 && decimal_code==3'b100);

  // Extremes of the adder
  cover property (decimal_code==3'd0 && mux_out==4'd0 && sum==7'd0);
  cover property (decimal_code==3'd7 && mux_out==4'd15 && sum==7'd22);

endmodule

bind priority_encoder_shift_register priority_encoder_shift_register_sva;