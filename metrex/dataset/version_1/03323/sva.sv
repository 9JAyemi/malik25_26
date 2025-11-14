//============================================================
// SVA for Counter
//============================================================
module Counter_chk #(
  parameter int Width     = 32,
  parameter bit Limited   = 0,
  parameter bit Down      = 0,
  parameter logic [Width-1:0] Initial = {Width{1'bx}}
) (
  input  logic                 Clock, Reset, Set, Load, Enable,
  input  logic [Width-1:0]     In,
  input  logic [Width-1:0]     Count
);
  localparam logic [Width-1:0] MAX  = {Width{1'b1}};
  localparam logic [Width-1:0] ZERO = '0;
  localparam bit               NoLimit = !Limited;

  // Async reset must immediately drive Initial
  a_async_reset: assert property (@(posedge Reset) Count === Initial);

  // One concise, complete cycle-accurate update rule
  a_update: assert property (@(posedge Clock) disable iff (Reset)
    Count === (
      (Load | (Enable & (NoLimit | (Down ? $past(Count) : ~&$past(Count))))) ?
        (Load ? In : (Down ? ($past(Count) - 1) : ($past(Count) + 1))) :
        $past(Count)
    )
  );

  // Load has priority over Enable
  a_load_prio: assert property (@(posedge Clock) disable iff (Reset)
    Load |-> (Count === In)
  );

  // Saturation (Limited=1): hold at boundaries
  a_sat_up_hold:   assert property (@(posedge Clock) disable iff (Reset)
    (Limited && !Down && Enable && !Load && ($past(Count) == MAX))  |-> (Count === $past(Count))
  );
  a_sat_down_hold: assert property (@(posedge Clock) disable iff (Reset)
    (Limited &&  Down && Enable && !Load && ($past(Count) == ZERO)) |-> (Count === $past(Count))
  );

  // Wrap (Limited=0): wrap at boundaries
  a_wrap_up:   assert property (@(posedge Clock) disable iff (Reset)
    (!Limited && !Down && Enable && !Load && ($past(Count) == MAX))  |-> (Count === ZERO)
  );
  a_wrap_down: assert property (@(posedge Clock) disable iff (Reset)
    (!Limited &&  Down && Enable && !Load && ($past(Count) == ZERO)) |-> (Count === MAX)
  );

  // Coverage
  c_reset:           cover property (@(posedge Reset) 1);
  c_load:            cover property (@(posedge Clock) !Reset && Load);
  c_inc:             cover property (@(posedge Clock) !Reset && !Down && Enable && !Load);
  c_dec:             cover property (@(posedge Clock) !Reset &&  Down && Enable && !Load);
  c_sat_up_hold:     cover property (@(posedge Clock) Limited && !Down && Enable && !Load && ($past(Count)==MAX));
  c_sat_down_hold:   cover property (@(posedge Clock) Limited &&  Down && Enable && !Load && ($past(Count)==ZERO));
  c_wrap_up:         cover property (@(posedge Clock) !Limited && !Down && Enable && !Load && ($past(Count)==MAX));
  c_wrap_down:       cover property (@(posedge Clock) !Limited &&  Down && Enable && !Load && ($past(Count)==ZERO));
endmodule

// Bind to all Counter instances (parameters forwarded)
bind Counter Counter_chk #(
  .Width  (Width),
  .Limited(Limited),
  .Down   (Down),
  .Initial(Initial)
) Counter_chk_i (
  .Clock (Clock),
  .Reset (Reset),
  .Set   (Set),
  .Load  (Load),
  .Enable(Enable),
  .In    (In),
  .Count (Count)
);


//============================================================
// SVA for Register
//============================================================
module Register_chk #(
  parameter int Width     = 32,
  parameter logic [Width-1:0] Initial = {Width{1'bx}}
) (
  input  logic                 Clock, Reset, Set, Enable,
  input  logic [Width-1:0]     In,
  input  logic [Width-1:0]     Out
);
  // Async reset must immediately drive Initial
  a_async_reset: assert property (@(posedge Reset) Out === Initial);

  // Cycle-accurate update rule
  a_update: assert property (@(posedge Clock) disable iff (Reset)
    Out === (Enable ? In : $past(Out))
  );

  // Set is ignored by design (no effect without Enable)
  a_set_ignored: assert property (@(posedge Clock) disable iff (Reset)
    (!Enable && $changed(Set)) |-> (Out === $past(Out))
  );

  // Coverage
  c_reset:   cover property (@(posedge Reset) 1);
  c_enable:  cover property (@(posedge Clock) !Reset && Enable);
  c_hold:    cover property (@(posedge Clock) !Reset && !Enable);
endmodule

// Bind to all Register instances (parameters forwarded)
bind Register Register_chk #(
  .Width  (Width),
  .Initial(Initial)
) Register_chk_i (
  .Clock (Clock),
  .Reset (Reset),
  .Set   (Set),
  .Enable(Enable),
  .In    (In),
  .Out   (Out)
);