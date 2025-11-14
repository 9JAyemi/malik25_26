// SVA checker for altera_up_av_config_auto_init_d5m
// Focus: end-to-end decode correctness, packer correctness, X-checks, and concise coverage.

module altera_up_av_config_auto_init_d5m_sva
  #(parameter D5M_COLUMN_SIZE = 16'd2591,
              D5M_ROW_SIZE    = 16'd1943,
              D5M_COLUMN_BIN  = 16'h0000,
              D5M_ROW_BIN     = 16'h0000)
(
  input  logic [4:0]  rom_address,
  input  logic [15:0] exposure,
  input  logic [35:0] rom_data,
  input  logic [31:0] data
);

  // Expected 32-bit data for each address (mirrors DUT)
  function automatic logic [31:0] exp_data32(input logic [4:0] addr, input logic [15:0] exp);
    case (addr)
      5'd0  : exp_data32 = {8'hBA, 8'h00, 16'h0000};
      5'd1  : exp_data32 = {8'hBA, 8'h20, 16'hc000};
      5'd2  : exp_data32 = {8'hBA, 8'h09, exp};
      5'd3  : exp_data32 = {8'hBA, 8'h05, 16'h0000};
      5'd4  : exp_data32 = {8'hBA, 8'h06, 16'h0019};
      5'd5  : exp_data32 = {8'hBA, 8'h0A, 16'h8000};
      5'd6  : exp_data32 = {8'hBA, 8'h2B, 16'h000b};
      5'd7  : exp_data32 = {8'hBA, 8'h2C, 16'h000f};
      5'd8  : exp_data32 = {8'hBA, 8'h2D, 16'h000f};
      5'd9  : exp_data32 = {8'hBA, 8'h2E, 16'h000b};
      5'd10 : exp_data32 = {8'hBA, 8'h10, 16'h0051};
      5'd11 : exp_data32 = {8'hBA, 8'h11, 16'h1807};
      5'd12 : exp_data32 = {8'hBA, 8'h12, 16'h0002};
      5'd13 : exp_data32 = {8'hBA, 8'h10, 16'h0053};
      5'd14 : exp_data32 = {8'hBA, 8'h98, 16'h0000};
`ifdef ENABLE_TEST_PATTERN
      5'd15 : exp_data32 = {8'hBA, 8'hA0, 16'h0001};
      5'd16 : exp_data32 = {8'hBA, 8'hA1, 16'h0123};
      5'd17 : exp_data32 = {8'hBA, 8'hA2, 16'h0456};
`else
      5'd15 : exp_data32 = {8'hBA, 8'hA0, 16'h0000};
      5'd16 : exp_data32 = {8'hBA, 8'hA1, 16'h0000};
      5'd17 : exp_data32 = {8'hBA, 8'hA2, 16'h0FFF};
`endif
      5'd18 : exp_data32 = {8'hBA, 8'h01, 16'h0036};
      5'd19 : exp_data32 = {8'hBA, 8'h02, 16'h0010};
      5'd20 : exp_data32 = {8'hBA, 8'h03, D5M_ROW_SIZE};
      5'd21 : exp_data32 = {8'hBA, 8'h04, D5M_COLUMN_SIZE};
      5'd22 : exp_data32 = {8'hBA, 8'h22, D5M_ROW_BIN};
      5'd23 : exp_data32 = {8'hBA, 8'h23, D5M_COLUMN_BIN};
      5'd24 : exp_data32 = {8'hBA, 8'h49, 16'h01A8};
      default: exp_data32 = {8'h00, 8'h00, 16'h0000};
    endcase
  endfunction

  // Pack 32b -> 36b with zero gaps (mirrors DUT)
  function automatic logic [35:0] pack32to36(input logic [31:0] d);
    return {d[31:24], 1'b0, d[23:16], 1'b0, d[15:8], 1'b0, d[7:0], 1'b0};
  endfunction

  // Asynchronous checks (no clock in DUT)
  always_comb begin
    // X/Z checks
    assert (!$isunknown({rom_address, exposure})) else $error("X/Z on inputs: rom_address=%b exposure=%b", rom_address, exposure);
    assert (!$isunknown(rom_data)) else $error("X/Z on rom_data=%b", rom_data);

    // Ensure gap bits are zero
    assert (rom_data[27] == 1'b0 && rom_data[18] == 1'b0 && rom_data[9] == 1'b0 && rom_data[0] == 1'b0)
      else $error("rom_data gap bits not zero: %b", rom_data);

    // End-to-end: decode + pack must match output
    logic [31:0] exp32 = exp_data32(rom_address, exposure);
    logic [35:0] exp36 = pack32to36(exp32);
    assert (rom_data == exp36)
      else $error("rom_data mismatch: addr=%0d exp32=%h exp36=%h got=%h", rom_address, exp32, exp36, rom_data);

    // Internal data must pack to rom_data (checks packer correctness relative to internal reg)
    assert (rom_data == pack32to36(data))
      else $error("packer mismatch: data=%h packed=%h rom_data=%h", data, pack32to36(data), rom_data);

    // Sanity: for valid table entries, high byte is 8'hBA; default is 0
    if (rom_address <= 5'd24)
      assert (exp32[31:24] == 8'hBA) else $error("MSB byte not 8'hBA for addr=%0d exp32=%h", rom_address, exp32);
    else
      assert (exp32 == 32'h0000_0000) else $error("Default case not zero for addr=%0d exp32=%h", rom_address, exp32);

    // Concise functional coverage
    for (int i = 0; i < 32; i++) begin
      cover (rom_address == i);
    end
    // Exposure extremes at the only address that uses it
    cover (rom_address == 5'd2 && exposure == 16'h0000);
    cover (rom_address == 5'd2 && exposure == 16'hFFFF);
  end

endmodule

// Bind the SVA checker to the DUT
bind altera_up_av_config_auto_init_d5m
  altera_up_av_config_auto_init_d5m_sva
  #(.D5M_COLUMN_SIZE(D5M_COLUMN_SIZE),
    .D5M_ROW_SIZE   (D5M_ROW_SIZE),
    .D5M_COLUMN_BIN (D5M_COLUMN_BIN),
    .D5M_ROW_BIN    (D5M_ROW_BIN))
  i_altera_up_av_config_auto_init_d5m_sva
  ( .rom_address(rom_address),
    .exposure   (exposure),
    .rom_data   (rom_data),
    .data       (data) );