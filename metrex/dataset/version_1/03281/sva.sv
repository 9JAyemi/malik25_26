// SVA checker for MULTIPLEXER_4_TO_1
module MULTIPLEXER_4_TO_1_sva #(
  parameter BUS_WIDTH = 32
) (
  input logic [BUS_WIDTH-1:0] IN1,
  input logic [BUS_WIDTH-1:0] IN2,
  input logic [BUS_WIDTH-1:0] IN3,
  input logic [BUS_WIDTH-1:0] IN4,
  input logic [1:0]           SELECT,
  input logic [BUS_WIDTH-1:0] OUT
);

  // Use a global sampling event for combinational checks
  default clocking cb @(posedge $global_clock); endclocking

  // SELECT must never be X/Z (prevents unintended latch behavior)
  a_select_known: assert property ( !$isunknown(SELECT) )
    else $error("MUX4x1: SELECT has X/Z");

  // Functional correctness: OUT must equal the selected input
  a_mux_correct: assert property (
    !$isunknown(SELECT) |->
      ((SELECT==2'b00 && OUT===IN1) ||
       (SELECT==2'b01 && OUT===IN2) ||
       (SELECT==2'b10 && OUT===IN3) ||
       (SELECT==2'b11 && OUT===IN4))
  ) else $error("MUX4x1: OUT != selected input");

  // No spurious OUT changes when inputs and SELECT are stable
  a_no_spurious: assert property (
    $stable({IN1,IN2,IN3,IN4,SELECT}) |-> $stable(OUT)
  ) else $error("MUX4x1: OUT changed despite stable inputs/SELECT");

  // When SELECT is stable and the selected input changes, OUT must update immediately (##0)
  a_selected_change_updates_out: assert property (
    !$isunknown(SELECT) && $stable(SELECT) &&
    ((SELECT==2'b00 && $changed(IN1)) ||
     (SELECT==2'b01 && $changed(IN2)) ||
     (SELECT==2'b10 && $changed(IN3)) ||
     (SELECT==2'b11 && $changed(IN4)))
    |-> ##0
    ((SELECT==2'b00 && $changed(OUT) && OUT===IN1) ||
     (SELECT==2'b01 && $changed(OUT) && OUT===IN2) ||
     (SELECT==2'b10 && $changed(OUT) && OUT===IN3) ||
     (SELECT==2'b11 && $changed(OUT) && OUT===IN4))
  ) else $error("MUX4x1: Selected input change not reflected on OUT");

  // Unselected input changes must not affect OUT (guard that selected input is stable)
  a_unselected_change_no_glitch: assert property (
    !$isunknown(SELECT) &&
    ((SELECT==2'b00 && $stable(IN1) && ($changed(IN2)||$changed(IN3)||$changed(IN4))) ||
     (SELECT==2'b01 && $stable(IN2) && ($changed(IN1)||$changed(IN3)||$changed(IN4))) ||
     (SELECT==2'b10 && $stable(IN3) && ($changed(IN1)||$changed(IN2)||$changed(IN4))) ||
     (SELECT==2'b11 && $stable(IN4) && ($changed(IN1)||$changed(IN2)||$changed(IN3))))
    |-> ##0 $stable(OUT)
  ) else $error("MUX4x1: OUT glitched due to unselected input change");

  // Coverage: exercise all select values
  c_sel_00: cover property (SELECT==2'b00);
  c_sel_01: cover property (SELECT==2'b01);
  c_sel_10: cover property (SELECT==2'b10);
  c_sel_11: cover property (SELECT==2'b11);

  // Coverage: observe propagation from each selected input to OUT
  c_path_00: cover property ( $stable(SELECT) && SELECT==2'b00 && $changed(IN1) ##0 $changed(OUT) );
  c_path_01: cover property ( $stable(SELECT) && SELECT==2'b01 && $changed(IN2) ##0 $changed(OUT) );
  c_path_10: cover property ( $stable(SELECT) && SELECT==2'b10 && $changed(IN3) ##0 $changed(OUT) );
  c_path_11: cover property ( $stable(SELECT) && SELECT==2'b11 && $changed(IN4) ##0 $changed(OUT) );

endmodule

// Bind the checker to the DUT
bind MULTIPLEXER_4_TO_1 MULTIPLEXER_4_TO_1_sva #(.BUS_WIDTH(BUS_WIDTH)) mux4to1_sva_b (.*);