// SVA for ssio_sdr_in
// Bind into DUT; accesses internal signals (clk_io, clk_int, output_q_reg)
module ssio_sdr_in_sva #(
  parameter string TARGET = "GENERIC",
  parameter string CLOCK_INPUT_STYLE = "BUFIO2",
  parameter int WIDTH = 1
) ();

  // past-valid for clk_io domain (no reset in DUT)
  bit past_valid_io;
  initial past_valid_io = 0;
  always @(posedge clk_io) past_valid_io <= 1;

  // Data capture: q follows d on clk_io; no X at capture; no glitches on q
  genvar i;
  generate
    for (i = 0; i < WIDTH; i++) begin : g_d2q
      ap_d_known: assert property (@(posedge clk_io) !$isunknown(input_d[i]));
      ap_q_known: assert property (@(posedge clk_io) !$isunknown(output_q[i]));
      ap_d2q:     assert property (@(posedge clk_io) disable iff (!past_valid_io)
                                   output_q[i] == $past(input_d[i]));
      // Any q bit change must coincide with a clk_io rising edge
      ap_q_change_on_clk: assert property (@(posedge output_q[i] or negedge output_q[i])
                                           disable iff (!past_valid_io) $rose(clk_io));
      // Coverage: data change gets captured next cycle
      cp_bit_cap: cover property (@(posedge clk_io) $changed(input_d[i]) ##1
                                  output_q[i] == $past(input_d[i]));
    end
  endgenerate

  // Port/reg connectivity
  ap_port_matches_reg: assert property (@(posedge clk_io) output_q == output_q_reg);

  // Clock relationships (match DUT structure)
  if (TARGET != "XILINX") begin
    ap_clk_eq_generic_a: assert property (@(posedge input_clk) clk_io == input_clk);
    ap_clk_eq_generic_b: assert property (@(posedge input_clk) output_clk == input_clk);
  end
  else if (CLOCK_INPUT_STYLE == "BUFG") begin
    ap_clk_eq_bufg_a: assert property (@(posedge output_clk) output_clk == clk_io);
    ap_clk_eq_bufg_b: assert property (@(posedge clk_io) output_clk == clk_io);
  end
  else if (CLOCK_INPUT_STYLE == "BUFIO2") begin
    // BUFG input is clk_int; check path integrity
    ap_clk_path_bufg: assert property (@(posedge output_clk) output_clk == clk_int);
  end
  else begin // BUFR or BUFIO: ensure clocks are clean at edges
    ap_clk_clean_io:  assert property (@(posedge clk_io)    !$isunknown(clk_io));
    ap_clk_clean_out: assert property (@(posedge output_clk) !$isunknown(output_clk));
  end

  // Basic activity coverage
  cp_cap:             cover property (@(posedge clk_io) $changed(input_d) ##1 output_q == $past(input_d));
  cp_clk_io_edge:     cover property (@(posedge clk_io) 1);
  cp_output_clk_edge: cover property (@(posedge output_clk) 1);

endmodule

bind ssio_sdr_in ssio_sdr_in_sva #(
  .TARGET(TARGET),
  .CLOCK_INPUT_STYLE(CLOCK_INPUT_STYLE),
  .WIDTH(WIDTH)
) u_ssio_sdr_in_sva();