// Bind this SVA to the DUT (connects to internal temp_data)
bind Counter7SD Counter7SD_sva #(
  .ZERO   (ZERO),   .ONE   (ONE),   .TWO   (TWO),   .THREE (THREE), .FOUR  (FOUR),
  .FIVE   (FIVE),   .SIX   (SIX),   .SEVEN (SEVEN), .EIGHT (EIGHT), .NINE  (NINE),
  .PAUSE  (PAUSE),  .HOLD  (HOLD)
) i_counter7sd_sva (
  .clock(clock), .reset(reset), .pause(pause), .reverse(reverse),
  .data(data), .temp_data(temp_data)
);

// SVA module
module Counter7SD_sva #(
  parameter logic [6:0] ZERO, ONE, TWO, THREE, FOUR, FIVE, SIX, SEVEN, EIGHT, NINE,
                        PAUSE, HOLD
)(
  input  logic        clock,
  input  logic        reset,
  input  logic        pause,
  input  logic        reverse,
  input  logic [6:0]  data,
  input  logic [6:0]  temp_data
);

  // Helpers
  function automatic logic is_digit(input logic [6:0] v);
    return v inside {ZERO,ONE,TWO,THREE,FOUR,FIVE,SIX,SEVEN,EIGHT,NINE};
  endfunction

  function automatic logic in_set_data(input logic [6:0] v);
    return v inside {PAUSE,HOLD,ZERO,ONE,TWO,THREE,FOUR,FIVE,SIX,SEVEN,EIGHT,NINE};
  endfunction

  function automatic logic [6:0] next_state(
    input logic [6:0] cur, input logic pause_i, input logic reset_i, input logic reverse_i
  );
    if (!reset_i)              next_state = HOLD;
    else if (!pause_i)         next_state = cur;
    else begin
      unique case (cur)
        HOLD:   next_state = reverse_i ? NINE  : ZERO;
        ZERO:   next_state = reverse_i ? NINE  : ONE;
        ONE:    next_state = reverse_i ? ZERO  : TWO;
        TWO:    next_state = reverse_i ? ONE   : THREE;
        THREE:  next_state = reverse_i ? TWO   : FOUR;
        FOUR:   next_state = reverse_i ? THREE : FIVE;
        FIVE:   next_state = reverse_i ? FOUR  : SIX;
        SIX:    next_state = reverse_i ? FIVE  : SEVEN;
        SEVEN:  next_state = reverse_i ? SIX   : EIGHT;
        EIGHT:  next_state = reverse_i ? SEVEN : NINE;
        NINE:   next_state = reverse_i ? EIGHT : ZERO;
        default: next_state = HOLD;
      endcase
    end
  endfunction

  // Data output must reflect previous-cycle inputs (due to nonblocking assignments)
  // data(t) == (pause(t-1)? temp_data(t-1) : PAUSE)
  property p_data_mux;
    @(posedge clock)
      !$isunknown($past(pause)) && !$isunknown($past(temp_data))
      |-> data == (($past(pause)==1'b0) ? PAUSE : $past(temp_data));
  endproperty
  assert property(p_data_mux);

  // temp_data implements the specified FSM based on previous-cycle inputs
  property p_nextstate;
    @(posedge clock)
      !$isunknown({$past(reset),$past(pause),$past(reverse),$past(temp_data)})
      |-> temp_data == next_state($past(temp_data), $past(pause), $past(reset), $past(reverse));
  endproperty
  assert property(p_nextstate);

  // Legal encodings only
  assert property (@(posedge clock) temp_data inside {HOLD,ZERO,ONE,TWO,THREE,FOUR,FIVE,SIX,SEVEN,EIGHT,NINE});
  assert property (@(posedge clock) in_set_data(data));

  // Specific quick checks
  // Synchronous active-low reset drives HOLD next cycle
  assert property (@(posedge clock) !$isunknown($past(reset)) && ($past(reset)==1'b0) |-> temp_data==HOLD);

  // When not paused (pause==0), temp_data holds its value (unless reset asserted)
  assert property (@(posedge clock)
    !$isunknown({$past(reset),$past(pause),$past(temp_data)}) &&
    ($past(reset)==1'b1) && ($past(pause)==1'b0)
    |-> temp_data == $past(temp_data)
  );

  // Coverage
  // Reachability of states (note: some may alias due to equal encodings)
  cover property (@(posedge clock) temp_data==HOLD);
  cover property (@(posedge clock) temp_data==ZERO);
  cover property (@(posedge clock) temp_data==ONE);
  cover property (@(posedge clock) temp_data==TWO);
  cover property (@(posedge clock) temp_data==THREE);
  cover property (@(posedge clock) temp_data==FOUR);
  cover property (@(posedge clock) temp_data==FIVE);
  cover property (@(posedge clock) temp_data==SIX);
  cover property (@(posedge clock) temp_data==SEVEN);
  cover property (@(posedge clock) temp_data==EIGHT);
  cover property (@(posedge clock) temp_data==NINE);

  // Exit HOLD forward/backward when unpaused
  cover property (@(posedge clock)
    $past(reset)==1 && $past(pause)==1 && $past(temp_data)==HOLD && $past(reverse)==0 ##1 temp_data==ZERO
  );
  cover property (@(posedge clock)
    $past(reset)==1 && $past(pause)==1 && $past(temp_data)==HOLD && $past(reverse)==1 ##1 temp_data==NINE
  );

  // Wrap-around transitions
  cover property (@(posedge clock)
    $past(reset)==1 && $past(pause)==1 && $past(temp_data)==NINE && $past(reverse)==0 ##1 temp_data==ZERO
  );
  cover property (@(posedge clock)
    $past(reset)==1 && $past(pause)==1 && $past(temp_data)==ZERO && $past(reverse)==1 ##1 temp_data==NINE
  );

  // Data gating coverage
  cover property (@(posedge clock) $past(pause)==0 ##1 data==PAUSE);
  cover property (@(posedge clock) $past(pause)==1 ##1 data==$past(temp_data));

  // Recovery from illegal encoding goes to HOLD when counting
  cover property (@(posedge clock)
    $past(reset)==1 && $past(pause)==1 &&
    !($past(temp_data) inside {HOLD,ZERO,ONE,TWO,THREE,FOUR,FIVE,SIX,SEVEN,EIGHT,NINE})
    ##1 temp_data==HOLD
  );

endmodule