// SVA for divider: bind into DUT; focuses on key handshakes, FSM, datapath, and coverage.
`ifndef DIVIDER_SVA
`define DIVIDER_SVA

bind divider divider_sva();
module divider_sva();

  // Clocking and reset
  default clocking cb @(posedge clk); endclocking

  // Reset behavior (do not disable on reset)
  assert property (@(posedge clk) rst |=> (state==get_a && !s_input_a_ack && !s_input_b_ack && !s_output_z_stb));

  // Disable the rest during reset
  default disable iff (rst);

  // Basic sanity
  assert property (1'b1 |-> state <= put_z);
  assert property (1'b1 |-> output_z_stb==s_output_z_stb && input_a_ack==s_input_a_ack && input_b_ack==s_input_b_ack && output_z==s_output_z);
  assert property (s_output_z_stb |-> !$isunknown(s_output_z));
  assert property (!(s_input_a_ack && s_input_b_ack));

  // A handshakes (ready/valid) and capture
  assert property (s_input_a_ack |-> state==get_a);
  assert property (state==get_a && s_input_a_ack && !input_a_stb |=> state==get_a && s_input_a_ack);
  assert property (state==get_a && s_input_a_ack && input_a_stb |=> state==get_b && !s_input_a_ack && a==$past(input_a));

  // B handshakes (ready/valid) and capture
  assert property (s_input_b_ack |-> state==get_b);
  assert property (state==get_b && s_input_b_ack && !input_b_stb |=> state==get_b && s_input_b_ack);
  assert property (state==get_b && s_input_b_ack && input_b_stb |=> state==unpack && !s_input_b_ack && b==$past(input_b));

  // Output handshake and hold
  assert property (s_output_z_stb |-> state==put_z);
  assert property (state==put_z && s_output_z_stb && !output_z_ack |=> state==put_z && s_output_z_stb && $stable(s_output_z));
  assert property (state==put_z && s_output_z_stb && output_z_ack |=> state==get_a && !s_output_z_stb);

  // Forward progress (B captured -> result valid within a bounded time)
  assert property (state==get_b && s_input_b_ack && input_b_stb |-> ##[1:300] s_output_z_stb);

  // Unpack -> special_cases and field extraction
  assert property (state==unpack |=> state==special_cases);
  assert property ($past(state)==unpack && state==special_cases |-> a_m==$past(a[22:0]) && b_m==$past(b[22:0]) &&
                                             a_e==$past(a[30:23])-127 && b_e==$past(b[30:23])-127 &&
                                             a_s==$past(a[31]) && b_s==$past(b[31]));

  // special_cases transitions are only to put_z or normalise_a
  assert property (state==special_cases |=> (state==put_z || state==normalise_a));

  // Divide initialization
  assert property (state==divide_0 |=> state==divide_1 &&
                   z_s == ($past(a_s) ^ $past(b_s)) &&
                   z_e == $past(a_e) - $past(b_e) &&
                   quotient==0 && remainder==0 && count==0 &&
                   dividend == ($past(a_m) << 27) && divisor == $past(b_m));

  // Divide loop control
  assert property (state==divide_2 && count<49 |=> state==divide_1 && count==$past(count)+1);
  assert property (state==divide_2 && count==49 |=> state==divide_3);
  assert property ((state==divide_1 || state==divide_2 || state==divide_3) |-> count<=49);

  // Transfer quotient/flags
  assert property (state==divide_3 |=> state==normalise_1 &&
                   z_m==$past(quotient[26:3]) &&
                   guard==$past(quotient[2]) &&
                   round_bit==$past(quotient[1]) &&
                   sticky==($past(quotient[0]) | ($past(remainder)!=0)));

  // normalise_1 behavior
  assert property (state==normalise_1 && (z_m[23]==0) && ($signed(z_e)>-126) |=> 
                   z_e==$past(z_e)-1 &&
                   z_m=={ $past(z_m[22:0]), $past(guard) } &&
                   guard==$past(round_bit) &&
                   round_bit==0);
  assert property (state==normalise_1 && !((z_m[23]==0) && ($signed(z_e)>-126)) |=> state==normalise_2);

  // normalise_2 behavior
  assert property (state==normalise_2 && ($signed(z_e)<-126) |=> 
                   z_e==$past(z_e)+1 &&
                   z_m==($past(z_m)>>1) &&
                   guard==$past(z_m[0]) &&
                   round_bit==$past(guard) &&
                   sticky==($past(sticky)|$past(round_bit)));
  assert property (state==normalise_2 && !($signed(z_e)<-126) |=> state==round);

  // Round step (increment and possible exponent bump)
  assert property (state==round |=> z_m == $past(z_m) + ( $past(guard) && ($past(round_bit) || $past(sticky) || $past(z_m[0])) ));
  assert property (state==round && $past(guard) && ($past(round_bit)||$past(sticky)||$past(z_m[0])) && $past(z_m)==24'hffffff |=> z_e==$past(z_e)+1);
  assert property (state==round |=> state==pack);

  // Pack -> put_z mapping (including special exponent cases)
  assert property (state==pack |=> state==put_z && s_output_z==$past(z));

  // Overflow to Inf
  assert property (state==pack && ($signed(z_e)>127) |=> s_output_z[30:23]==8'hFF && s_output_z[22:0]==0 && s_output_z[31]==$past(z_s));

  // Denormal result exponent zero
  assert property (state==pack && ($signed(z_e)==-126) && (z_m[23]==0) |=> s_output_z[30:23]==8'h00);

  // Normal pack fields (when not overflow or denorm-zero-exp case)
  assert property (state==pack && !($signed(z_e)>127) && !(($signed(z_e)==-126) && (z_m[23]==0)) |=> 
                   s_output_z[22:0]==$past(z_m[22:0]) &&
                   s_output_z[30:23]==($past(z_e[7:0])+8'd127) &&
                   s_output_z[31]==$past(z_s));

  // Only update captured regs on proper handshakes
  assert property ((a != $past(a)) |-> $past(state==get_a && s_input_a_ack && input_a_stb));
  assert property ((b != $past(b)) |-> $past(state==get_b && s_input_b_ack && input_b_stb));
  assert property ((s_output_z != $past(s_output_z)) |-> $past(state==put_z));

  // Coverage

  // Typical full transaction
  cover property (state==get_a && s_input_a_ack && input_a_stb ##[1:10]
                  state==get_b && s_input_b_ack && input_b_stb ##[1:300]
                  s_output_z_stb ##1 output_z_ack);

  // Exercise full divide loop
  cover property (state==divide_2 && count==49 ##1 state==divide_3 ##1 state==normalise_1);

  // Rounding that increments exponent
  cover property (state==round && guard && (round_bit || sticky || z_m[0]) && z_m==24'hffffff);

  // Denormal output (exp=0, mant!=0)
  cover property (state==put_z && s_output_z_stb && output_z[30:23]==8'h00 && output_z[22:0]!=0);

  // Overflow to infinity
  cover property (state==put_z && s_output_z_stb && output_z[30:23]==8'hFF && output_z[22:0]==0);

  // NaN result (exp=255, MSB of mantissa set)
  cover property (state==put_z && s_output_z_stb && output_z[30:23]==8'hFF && output_z[22]==1'b1);

endmodule
`endif