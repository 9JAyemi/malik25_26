// SVA for random_gen_v2
// Bind into DUT type: bind random_gen_v2 random_gen_v2_sva();

module random_gen_v2_sva;

  default clocking cb @ (posedge clock); endclocking

  // Helper
  let rc_mask = (retry_count >= 4'd9) ? 10'h3FF
                                      : ((10'h001 << (retry_count + 4'd1)) - 10'h001);

  // No X on key signals
  assert property (!$isunknown({reset, clock, init, enable, retry_count}));
  assert property (!$isunknown({trigger, random}));
  assert property (!$isunknown({random_sequence, slot_time_counter, random_counter}));

  // Reset values (checked each clock while reset=1)
  assert property (reset |-> random_sequence==10'd0 && slot_time_counter==8'd0 &&
                           random_counter==10'd0 && trigger==1'b1);

  // LFSR update
  assert property (disable iff (reset)
                   random_sequence == { $past(random_sequence)[8:0],
                                        ~($past(random_sequence)[2]^$past(random_sequence)[9]) });

  // Combinational mapping of random from retry_count/random_sequence
  assert property (random == (random_sequence & rc_mask));

  // slot_time_counter behavior
  assert property (disable iff (reset) init |=> slot_time_counter==8'd0);
  assert property (disable iff (reset) (!init && !trigger) |=> slot_time_counter == $past(slot_time_counter) + 8'd1);
  assert property (disable iff (reset) (!init &&  trigger) |=> slot_time_counter == $past(slot_time_counter));

  // random_counter behavior
  assert property (disable iff (reset) init |=> random_counter == $past(random));
  assert property (disable iff (reset) !enable |=> random_counter == 10'd0);
  assert property (disable iff (reset)
                   ( enable && (random_counter!=10'd0) && (slot_time_counter==8'd255) && !init)
                   |=> random_counter == $past(random_counter) - 10'd1);
  assert property (disable iff (reset)
                   ( enable && !( (random_counter!=10'd0) && (slot_time_counter==8'd255) ) && !init)
                   |=> random_counter == $past(random_counter));

  // trigger behavior and causes
  assert property (disable iff (reset) init |=> trigger==1'b0);
  assert property (disable iff (reset) !enable |=> trigger==1'b0);
  assert property (disable iff (reset) (enable && (random_counter==10'd0) && !init) |=> trigger==1'b1);
  assert property (disable iff (reset) (enable && (random_counter!=10'd0) && !init) |=> trigger==$past(trigger));
  assert property (disable iff (reset) $rose(trigger) |-> $past(enable && (random_counter==10'd0)));

  // Corner/wrap checks
  assert property (disable iff (reset)
                   (!init && !trigger && $past(slot_time_counter)==8'd255) |=> slot_time_counter==8'd0);

  // Functional coverage
  genvar i;
  generate
    for (i=0; i<=9; i++) begin : C_RC
      cover property (retry_count==i[3:0]);
    end
  endgenerate
  cover property (retry_count>=4'd10);                           // default case exercised
  cover property (disable iff (reset) !trigger ##1 slot_time_counter==8'd255 ##1 slot_time_counter==8'd0);
  cover property (disable iff (reset)
                  enable && (random_counter!=10'd0) && slot_time_counter==8'd255
                  ##1 random_counter==$past(random_counter)-10'd1);
  cover property (disable iff (reset)
                  enable && (random_counter==10'd0) ##1 trigger==1'b1);
  cover property (disable iff (reset)
                  !enable ##1 (random_counter==10'd0 && trigger==1'b0));

endmodule