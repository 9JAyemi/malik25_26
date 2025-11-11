// SVA checker for altera_up_av_config_auto_init_ltm
// Bind this into the DUT. Drive clk from your TB.

module altera_up_av_config_auto_init_ltm_sva (
  input logic              clk,
  input logic       [4:0]  rom_address,
  input logic      [23:0]  rom_data
);

  // Golden model of combinational mapping
  function automatic logic [23:0] exp_data (input logic [4:0] a);
    unique case (a)
      5'd0 : exp_data = {8'h00, 6'h02, 2'b00, 8'h07};
      5'd1 : exp_data = {8'h00, 6'h03, 2'b00, 8'hDF};
      5'd2 : exp_data = {8'h00, 6'h04, 2'b00, 8'h17};
      5'd3 : exp_data = {8'h00, 6'h11, 2'b00, 8'h00};
      5'd4 : exp_data = {8'h00, 6'h12, 2'b00, 8'h5B};
      5'd5 : exp_data = {8'h00, 6'h13, 2'b00, 8'hFF};
      5'd6 : exp_data = {8'h00, 6'h14, 2'b00, 8'h00};
      5'd7 : exp_data = {8'h00, 6'h15, 2'b00, 8'h20};
      5'd8 : exp_data = {8'h00, 6'h16, 2'b00, 8'h40};
      5'd9 : exp_data = {8'h00, 6'h17, 2'b00, 8'h80};
      5'd10: exp_data = {8'h00, 6'h18, 2'b00, 8'h00};
      5'd11: exp_data = {8'h00, 6'h19, 2'b00, 8'h80};
      5'd12: exp_data = {8'h00, 6'h1A, 2'b00, 8'h00};
      5'd13: exp_data = {8'h00, 6'h1B, 2'b00, 8'h00};
      5'd14: exp_data = {8'h00, 6'h1C, 2'b00, 8'h80};
      5'd15: exp_data = {8'h00, 6'h1D, 2'b00, 8'hC0};
      5'd16: exp_data = {8'h00, 6'h1E, 2'b00, 8'hE0};
      5'd17: exp_data = {8'h00, 6'h1F, 2'b00, 8'hFF};
      5'd18: exp_data = {8'h00, 6'h20, 2'b00, 8'hD2};
      5'd19: exp_data = {8'h00, 6'h21, 2'b00, 8'hD2};
      default: exp_data = 24'h000000;
    endcase
  endfunction

  // Core functional check: exact mapping for every address
  a_map_exact: assert property (@(posedge clk)
    rom_data == exp_data(rom_address)
  ) else $error("ROM mapping mismatch: addr=%0d data=%h exp=%h",
                rom_address, rom_data, exp_data(rom_address));

  // Structural invariants of encoding
  a_top_zero:  assert property (@(posedge clk) rom_data[23:16] == 8'h00);
  a_pad_zero:  assert property (@(posedge clk) rom_data[9:8]   == 2'b00);

  // Known-ness and stability
  a_known:     assert property (@(posedge clk)
                    !$isunknown(rom_address) |-> !$isunknown(rom_data));
  a_stable:    assert property (@(posedge clk)
                    $stable(rom_address) |-> $stable(rom_data));

  // Coverage: hit all defined addresses and default path
  genvar i;
  generate
    for (i = 0; i <= 19; i++) begin : C_DEF
      c_addr: cover property (@(posedge clk)
                 rom_address == i && rom_data == exp_data(i));
    end
  endgenerate
  c_default: cover property (@(posedge clk)
                (rom_address > 5'd19) && (rom_data == 24'h000000));

endmodule

// Bind into the DUT (ensure 'clk' exists in your TB scope)
bind altera_up_av_config_auto_init_ltm
  altera_up_av_config_auto_init_ltm_sva u_altera_up_av_config_auto_init_ltm_sva (
    .clk($global_clock), // or replace with your TB clock
    .rom_address(rom_address),
    .rom_data(rom_data)
  );