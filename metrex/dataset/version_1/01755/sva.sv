// SVA for clock_bootstrap_rom
// Bind this checker to your DUT. Provide a sampling clock and async active-low reset.
// If you have no reset, tie rst_n permanently high.

package clock_bootstrap_rom_sva_pkg;
  function automatic bit in_range(input logic [15:0] a);
    return (a[15:4] == 12'h0);
  endfunction

  function automatic logic [47:0] expected_data(input logic [15:0] a);
    case (a[3:0])
      4'h0: 48'h0000_0C00_0F03;
      4'h1: 48'h1014_0000_0000;
      4'h2: 48'h1018_0000_0001;
      4'h3: 48'h1010_0000_3418;
      4'h4: 48'h1000_0000_0010;
      4'h5: 48'h1010_0000_3518;
      default: 48'hffff_ffff_ffff;
    endcase
  endfunction
endpackage

module clock_bootstrap_rom_sva
(
  input logic        clk,
  input logic        rst_n,
  input logic [15:0] addr,
  input logic [47:0] data
);
  import clock_bootstrap_rom_sva_pkg::*;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Sanity: no X/Z on addr, in-range addressing only
  a_addr_no_x:        assert property (!$isunknown(addr));
  a_addr_in_range:    assert property (in_range(addr));

  // Data must be known and match ROM contents for all valid addresses, zero-latency
  a_data_no_x_when_valid: assert property (in_range(addr) |-> !$isunknown(data));
  a_data_maps_correctly:  assert property (in_range(addr) |-> data == expected_data(addr));

  // Also ensure previous cycle mapped correctly (guards against transient mismaps)
  a_prev_cycle_correct:   assert property (in_range($past(addr)) |-> $past(data) == expected_data($past(addr)));

  // Coverage: hit every address 0..15 at least once
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : g_cov_addr
      c_addr_seen: cover property (in_range(addr) && addr[3:0] == i[3:0]);
    end
  endgenerate

  // Coverage: observe both special entries (0..5) and default entries (6..15)
  c_special_entries_seen: cover property (in_range(addr) && addr[3:0] inside {4'h0,4'h1,4'h2,4'h3,4'h4,4'h5});
  c_default_entries_seen: cover property (in_range(addr) && addr[3:0] inside {4'h6,4'h7,4'h8,4'h9,4'hA,4'hB,4'hC,4'hD,4'hE,4'hF});

endmodule

// Example bind (adjust clock/reset nets as appropriate):
// bind clock_bootstrap_rom clock_bootstrap_rom_sva u_rom_sva (.clk(tb_clk), .rst_n(tb_rst_n), .addr(addr), .data(data));