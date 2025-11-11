// SVA for up_down_shift
// Bind-friendly: taps DUT ports and internal regs
module up_down_shift_sva (
  input  logic        CLK,
  input  logic        RESET,
  input  logic        UP_DOWN,
  input  logic [3:0]  LOAD,
  input  logic [3:0]  D,
  input  logic [3:0]  OUT,
  input  logic [3:0]  up_down_counter,
  input  logic [3:0]  shift_register
);

  default clocking cb @(posedge CLK); endclocking

  // Basic sanity: no X/Z on controls and data inputs
  a_no_x_inputs: assert property (!$isunknown({RESET, UP_DOWN, LOAD, D}));

  // Synchronous reset drives all regs low
  a_reset: assert property (RESET |-> (up_down_counter==4'b0 && shift_register==4'b0 && OUT==4'b0));

  // LOAD (non-zero) path: load counter and shift reg from inputs; OUT uses previous sum (one-cycle lag)
  a_load: assert property (
    (!RESET && $past(!RESET) && $past(LOAD!=4'b0))
    |-> ( up_down_counter==$past(LOAD)
       && shift_register==$past(D)
       && OUT==$past(up_down_counter + shift_register))
  );

  // No-LOAD (LOAD==0) path: count up/down, shift left-in with D[0]; OUT uses previous sum (one-cycle lag)
  a_noload: assert property (
    (!RESET && $past(!RESET) && $past(LOAD==4'b0))
    |-> ( up_down_counter == ( ($past(up_down_counter) + ($past(UP_DOWN) ? 4'h1 : 4'hF)) & 4'hF )
       && shift_register == { $past(shift_register[2:0]), $past(D[0]) }
       && OUT == $past(up_down_counter + shift_register))
  );

  // Explicit wrap-around checks
  a_wrap_up:   assert property (!RESET && $past(!RESET) && $past(LOAD==4'b0) && $past(UP_DOWN)  && $past(up_down_counter)==4'hF |-> up_down_counter==4'h0);
  a_wrap_down: assert property (!RESET && $past(!RESET) && $past(LOAD==4'b0) && !$past(UP_DOWN) && $past(up_down_counter)==4'h0 |-> up_down_counter==4'hF);

  // Coverage
  c_reset_then_load: cover property (RESET ##1 !RESET ##1 (LOAD!=4'b0));
  c_load_event:      cover property (!RESET && $past(!RESET) && $past(LOAD!=4'b0));
  c_up_step:         cover property (!RESET && $past(!RESET) && $past(LOAD==4'b0) && $past(UP_DOWN));
  c_down_step:       cover property (!RESET && $past(!RESET) && $past(LOAD==4'b0) && !$past(UP_DOWN));
  c_shift_in_1:      cover property (!RESET && $past(!RESET) && $past(LOAD==4'b0) && $past(D[0])==1'b1);
  c_shift_in_0:      cover property (!RESET && $past(!RESET) && $past(LOAD==4'b0) && $past(D[0])==1'b0);
  c_wrap_up:         cover property (!RESET && $past(!RESET) && $past(LOAD==4'b0) && $past(UP_DOWN)  && $past(up_down_counter)==4'hF && up_down_counter==4'h0);
  c_wrap_down:       cover property (!RESET && $past(!RESET) && $past(LOAD==4'b0) && !$past(UP_DOWN) && $past(up_down_counter)==4'h0 && up_down_counter==4'hF);

endmodule

// Bind into the DUT (connects to ports and internal regs by name)
bind up_down_shift up_down_shift_sva sva (.*);