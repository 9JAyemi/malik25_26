// SVA checker for output_demux
module output_demux_sva #(parameter int C_FSM_SWITCH_WIDTH=20,
                          parameter int C_INTERFACE=0)
(
  input  logic [4:0]                           sel,
  input  logic                                 in_pin,
  input  logic [C_FSM_SWITCH_WIDTH-1:0]        out_pin
);

  // Build expected onehot from sel safely
  function automatic logic [C_FSM_SWITCH_WIDTH-1:0] sel2onehot(input logic [4:0] s);
    sel2onehot = '0;
    if (s < C_FSM_SWITCH_WIDTH) sel2onehot[s] = 1'b1;
  endfunction

  // Drive a combinational sampling event for concurrent assertions and coverage
  event comb_ev;
  always @(sel or in_pin or out_pin) -> comb_ev;
  default clocking cb @ (comb_ev); endclocking

  // Static parameter consistency with selected interface
  initial begin
    if (C_INTERFACE == 1) assert (C_FSM_SWITCH_WIDTH == 26)
      else                assert (C_FSM_SWITCH_WIDTH == 20);
  end

  // Inputs/outputs must be known (no X/Z)
  assert property ( !$isunknown({sel, in_pin}) );
  assert property ( !$isunknown(out_pin) );

  // Functional equivalence: exact demux behavior
  assert property ( out_pin == (in_pin ? sel2onehot(sel) : '0) );

  // Stronger structural checks (redundant with functional, but concise and clear)
  assert property ( (in_pin && (sel < C_FSM_SWITCH_WIDTH)) |-> $onehot(out_pin) );
  assert property ( (!in_pin || !(sel < C_FSM_SWITCH_WIDTH)) |-> (out_pin == '0) );

  // Coverage: each output index driven, disable path, and invalid sel path
  genvar i;
  generate
    for (i = 0; i < C_FSM_SWITCH_WIDTH; i++) begin : C_OV
      cover property ( in_pin && (sel == i) && out_pin[i] );
    end
  endgenerate
  cover property ( !in_pin && (out_pin == '0) );
  cover property ( in_pin && (sel >= C_FSM_SWITCH_WIDTH) && (out_pin == '0) );

endmodule

// Bind into DUT
bind output_demux output_demux_sva #(
  .C_FSM_SWITCH_WIDTH(C_FSM_SWITCH_WIDTH),
  .C_INTERFACE(C_INTERFACE)
) output_demux_sva_i (
  .sel(sel),
  .in_pin(in_pin),
  .out_pin(out_pin)
);