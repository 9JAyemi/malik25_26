// SVA for input_mux
// Bindable, parameter-aware, concise but with strong checking and coverage.

module input_mux_sva #(
  parameter int C_FSM_SWITCH_WIDTH = 20,
  parameter int C_INTERFACE = 0   // 0: Arduino (20), 1: RaspberryPi (26), default->Arduino
)(
  input  logic [4:0]                      sel,
  input  logic [C_FSM_SWITCH_WIDTH-1:0]   in_pin,
  input  logic                            out_int
);

  // Interface map width (how many sel codes are explicitly mapped in the RTL)
  localparam int MAP_WIDTH = (C_INTERFACE == 1) ? 26 : 20;
  // Effective valid select count is min(width of bus, map width)
  localparam int AVAIL     = (C_FSM_SWITCH_WIDTH < MAP_WIDTH) ? C_FSM_SWITCH_WIDTH : MAP_WIDTH;

  // Elaboration-time sanity checks (prevent out-of-range indices in RTL mapping)
  initial begin
    if (C_INTERFACE == 1 && C_FSM_SWITCH_WIDTH < 26)
      $error("input_mux parameter mismatch: RASPBERRYPI interface requires C_FSM_SWITCH_WIDTH >= 26");
    if (C_INTERFACE != 1 && C_FSM_SWITCH_WIDTH < 20)
      $error("input_mux parameter mismatch: ARDUINO interface requires C_FSM_SWITCH_WIDTH >= 20");
  end

  // Expected combinational function of the mux
  logic expected;
  always @* begin
    if (!$isunknown(sel) && (sel < AVAIL)) expected = in_pin[sel];
    else                                   expected = 1'b0;

    // Core functional check (4-state aware for X-propagation from selected input)
    assert (out_int === expected)
      else $error("input_mux: out_int mismatch. sel=%0d expected=%b got=%b", sel, expected, out_int);
  end

  // If selected input is known, output must be known and 2-state equal
  always @* if (!$isunknown(sel) && (sel < AVAIL) && !$isunknown(in_pin[sel]))
    assert (out_int == in_pin[sel])
      else $error("input_mux: known selected bit must drive known out_int. sel=%0d in=%b out=%b",
                  sel, in_pin[sel], out_int);

  // Unknown or illegal select must drive default 0 in this RTL
  always @* if ($isunknown(sel))
    assert (out_int === 1'b0)
      else $error("input_mux: unknown sel must produce default 0. out=%b", out_int);

  always @* if (!$isunknown(sel) && (sel >= AVAIL))
    assert (out_int === 1'b0)
      else $error("input_mux: sel out of range must produce default 0. sel=%0d out=%b", sel, out_int);

  // Basic hazard check: with sel held at i, out must track in_pin[i] immediately (##0)
  // Using immediate form via always @* already enforces zero-delay consistency above.

  // Coverage
  genvar i;
  generate
    for (i = 0; i < MAP_WIDTH; i++) begin : COV
      if (i < C_FSM_SWITCH_WIDTH) begin
        // Hit each legal select value at least once
        cover property (@(sel) sel == i);

        // See both output values while selecting each legal input
        cover property (@(sel or in_pin[i]) (sel == i) && (out_int == 1'b0));
        cover property (@(sel or in_pin[i]) (sel == i) && (out_int == 1'b1));
      end
    end
  endgenerate

  // Cover default behavior for illegal/unknown selects
  cover property (@(sel) (!$isunknown(sel) && sel >= AVAIL) && (out_int == 1'b0));
  cover property (@(sel) ($isunknown(sel) && (out_int == 1'b0)));

endmodule

// Example bind (place in a separate file or after the DUT definition):
// bind input_mux input_mux_sva #(.C_FSM_SWITCH_WIDTH(C_FSM_SWITCH_WIDTH),
//                                .C_INTERFACE(C_INTERFACE)) input_mux_sva_b (.*);