// SVA for shift_reg — concise, high-quality checks and coverage
`ifndef SHIFT_REG_SVA
`define SHIFT_REG_SVA

module shift_reg_sva #(parameter int reg_length = 150) ();

  // State encodings from DUT
  localparam [1:0] idle=2'b00, reading=2'b01, finished=2'b10, finished_and_waiting=2'b11;

  default clocking cb @(posedge baud_clk); endclocking
  default disable iff (rst);

  // Parameter sanity (must support [6:0] check)
  initial begin
    assert (reg_length >= 7)
      else $error("shift_reg: reg_length must be >= 7");
  end

  // Async reset effects
  ap_rst_regs: assert property (@(posedge rst)
      bitShiftReg == {reg_length{1'b1}} &&
      shifted_bus == {reg_length{1'b1}} &&
      current_state == idle);

  // Bit-shift behavior
  function automatic logic [reg_length-1:0] shift_next (logic [reg_length-1:0] cur, logic in);
    return {cur[reg_length-2:0], in};
  endfunction

  ap_shift: assert property ($past(!rst) |-> bitShiftReg == shift_next($past(bitShiftReg), $past(rx)));

  // FSM next-state behavior
  ap_idle_rx1: assert property ($past(!rst) && $past(current_state)==idle    && $past(rx)==1 |-> current_state==idle);
  ap_idle_rx0: assert property ($past(!rst) && $past(current_state)==idle    && $past(rx)==0 |-> current_state==reading);
  ap_read_keep: assert property ($past(!rst) && $past(current_state)==reading && !($past(bitShiftReg[6:0])==7'b1111111) |-> current_state==reading);
  ap_read_to_fin: assert property ($past(!rst) && $past(current_state)==reading &&  ($past(bitShiftReg[6:0])==7'b1111111) |-> current_state==finished);
  ap_fin_to_faw: assert property ($past(!rst) && $past(current_state)==finished |-> current_state==finished_and_waiting);
  ap_faw_to_idle: assert property ($past(!rst) && $past(current_state)==finished_and_waiting |-> current_state==idle);

  // State legality
  ap_state_legal: assert property (current_state inside {idle,reading,finished,finished_and_waiting});

  // finished_rx relationship and pulse width
  ap_frx_def: assert property (finished_rx == (current_state==finished));
  ap_frx_one_cycle: assert property ($rose(finished_rx) |=> !finished_rx);
  ap_frx_origin: assert property ($past(!rst) && $rose(finished_rx)
                                  |-> $past(current_state)==reading && $past(bitShiftReg[6:0])==7'b1111111);

  // shifted_bus capture and hold
  ap_bus_cap: assert property (@(posedge finished_rx) disable iff (rst) shifted_bus == bitShiftReg);
  ap_bus_stable: assert property (!$rose(finished_rx) |-> $stable(shifted_bus));

  // No X on key controls after reset
  ap_no_x: assert property (!$isunknown({current_state, finished_rx, bitShiftReg[6:0], shifted_bus[6:0]}));

  // Coverage
  cp_full_path: cover property (current_state==idle && rx==0
                                ##1 current_state==reading
                                ##[1:$] current_state==finished
                                ##1 current_state==finished_and_waiting
                                ##1 current_state==idle);
  cp_frx_pulse: cover property ($rose(finished_rx));
  cp_bus_cap:   cover property (@(posedge finished_rx) shifted_bus == bitShiftReg);

endmodule

bind shift_reg shift_reg_sva #(.reg_length(reg_length)) u_shift_reg_sva();

`endif