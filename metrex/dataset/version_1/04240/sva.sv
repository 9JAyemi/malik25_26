// SVA checker for port_control
module port_control_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic        enable,
  input  logic [99:0] in_port,
  input  logic [99:0] out_port
);

  default clocking cb @(posedge clk); endclocking

  // 1) Synchronous reset clears output on next cycle
  a_reset_clears: assert property (reset |=> out_port == '0);

  // 2) When enabled (and not in reset), capture input on next cycle
  a_enable_transfers: assert property (
    disable iff (reset || $initstate)
      enable && !reset |=> out_port == $past(in_port)
  );

  // 3) When disabled (and not in reset), hold value
  a_hold_when_disabled: assert property (
    disable iff (reset || $initstate)
      !enable && !reset |=> out_port == $past(out_port)
  );

  // 4) Any change must be caused by reset or enable in the prior cycle
  a_change_has_cause: assert property (
    disable iff ($initstate)
      (out_port != $past(out_port)) |-> $past(reset || enable)
  );

  // Coverage
  c_reset_event:  cover property (reset ##1 out_port == '0);
  c_pass_through: cover property (!reset && enable ##1 out_port == $past(in_port));
  c_hold_event:   cover property (!reset && !enable ##1 out_port == $past(out_port));
  c_change_when_en: cover property (!reset && enable && (in_port != $past(in_port))
                                    ##1 (out_port != $past(out_port)));

endmodule

// Bind into DUT
bind port_control port_control_sva sva_port_control (
  .clk(clk),
  .reset(reset),
  .enable(enable),
  .in_port(in_port),
  .out_port(out_port)
);