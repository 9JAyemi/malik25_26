// SVA for complement_concat
// Bind this file to the DUT: bind complement_concat complement_concat_sva sva_i();

module complement_concat_sva;

  // Access DUT signals directly via bind scope
  // clk, data_in, comp_concat_out, data_out1, data_out2 are in DUT scope

  default clocking cb @(posedge clk); endclocking

  bit past_valid;
  always @(posedge clk) past_valid <= 1'b1;

  // Internal register behaviors
  a_data_out1: assert property (past_valid |-> data_out1 == $past(data_in[7:0]));
  a_data_out2_lsb: assert property (past_valid |-> data_out2[7:0] == ~ $past(data_in[15:8]));
  a_data_out2_zeroext: assert property (past_valid |-> data_out2[23:8] == '0);

  // Output equals 1-cycle-late function of input
  a_concat_from_input: assert property (
    past_valid |-> comp_concat_out == { $past(data_in[7:0]), 16'h0, ~ $past(data_in[15:8]) }
  );

  // Output equals concat of prior-cycle internal regs
  a_concat_from_regs: assert property (
    past_valid |-> comp_concat_out == { $past(data_out1), $past(data_out2) }
  );

  // Minimal functional coverage
  c_upper_zero: cover property (past_valid && (data_in[15:8]==8'h00)
                                |=> comp_concat_out[7:0]==8'hFF && comp_concat_out[23:8]=='0);
  c_upper_ff:   cover property (past_valid && (data_in[15:8]==8'hFF)
                                |=> comp_concat_out[7:0]==8'h00 && comp_concat_out[23:8]=='0);
  c_lowbyte_map: cover property (past_valid && $changed(data_in[7:0])
                                 |=> comp_concat_out[31:24]==$past(data_in[7:0]));

endmodule