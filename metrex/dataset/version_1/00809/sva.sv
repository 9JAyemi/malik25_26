// SVA checker for BROM. Bind or instantiate in your TB and provide a sampling clk.
module brom_sva (
  input logic                clk,
  input logic [7:1]          adr_i,
  input logic                stb_i,
  input logic                ack_o,
  input logic [15:0]         dat_o
);
  default clocking cb @(posedge clk); endclocking

  // Golden ROM model
  function automatic logic [15:0] rom_exp (input logic [7:1] a);
    case (a)
      7'd0:  rom_exp = 16'h0113;
      7'd1:  rom_exp = 16'h0000;
      7'd2:  rom_exp = 16'h01B7;
      7'd3:  rom_exp = 16'h0010;
      7'd4:  rom_exp = 16'h0113;
      7'd5:  rom_exp = 16'h0011;
      7'd6:  rom_exp = 16'h5213;
      7'd7:  rom_exp = 16'h0011;
      7'd8:  rom_exp = 16'h9123;
      7'd9:  rom_exp = 16'h0041;
      7'd10: rom_exp = 16'hF06F;
      7'd11: rom_exp = 16'hFF5F;
      default: rom_exp = 16'hCCCC;
    endcase
  endfunction

  // Sanity: no X/Z on IOs
  a_no_x:          assert property (!$isunknown({adr_i, stb_i, ack_o, dat_o}));

  // Handshake: ack mirrors stb combinationally
  a_ack_eq_stb:    assert property (ack_o == stb_i);

  // Data correctness for all addresses
  a_data_match:    assert property (dat_o == rom_exp(adr_i));

  // Purity: data depends only on address (independent of stb)
  a_data_stable_on_stable_addr: assert property ($stable(adr_i) |-> $stable(dat_o));
  a_data_indep_of_stb:          assert property ($stable(adr_i) && $changed(stb_i) |-> $stable(dat_o));

  // Functional coverage (concise, focuses on distinct ROM contents)
  cover_handshake: cover property (stb_i && ack_o);

  cover_a0:  cover property (stb_i && ack_o && adr_i == 7'd0);
  cover_a1:  cover property (stb_i && ack_o && adr_i == 7'd1);
  cover_a2:  cover property (stb_i && ack_o && adr_i == 7'd2);
  cover_a3:  cover property (stb_i && ack_o && adr_i == 7'd3);
  cover_a4:  cover property (stb_i && ack_o && adr_i == 7'd4);
  cover_a5:  cover property (stb_i && ack_o && adr_i == 7'd5);
  cover_a6:  cover property (stb_i && ack_o && adr_i == 7'd6);
  cover_a7:  cover property (stb_i && ack_o && adr_i == 7'd7);
  cover_a8:  cover property (stb_i && ack_o && adr_i == 7'd8);
  cover_a9:  cover property (stb_i && ack_o && adr_i == 7'd9);
  cover_a10: cover property (stb_i && ack_o && adr_i == 7'd10);
  cover_a11: cover property (stb_i && ack_o && adr_i == 7'd11);
  cover_def: cover property (stb_i && ack_o && (adr_i inside {[7'd12:7'd127]}));

endmodule

// Example bind (ensure a 'clk' is visible in the bind scope)
// bind BROM brom_sva u_brom_sva(.clk(clk), .adr_i(adr_i), .stb_i(stb_i), .ack_o(ack_o), .dat_o(dat_o));