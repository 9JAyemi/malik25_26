// SVA for nkmd_progrom
// Bind this module to the DUT to check/cover behavior.

module nkmd_progrom_sva(
  input logic        clk,
  input logic [31:0] addr_i,
  input logic [31:0] data_o
);

  // Track first valid cycle for $past usage
  logic past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Golden model of the ROM mapping (matches DUT semantics)
  function automatic logic [31:0] exp_data(input logic [31:0] a);
    if (a[31:16] != 16'h0000) return 32'h8001_0001;
    unique case (a[15:0])
      16'h0000: return 32'h0000_0000;
      16'h0001: return 32'h0000_0000;
      16'h0002: return 32'h0000_0000;
      16'h0003: return 32'h0000_0000;
      16'h0004: return 32'h0101_0001;
      16'h0005: return 32'h0201_0002;
      16'h0006: return 32'h0301_0003;
      16'h0007: return 32'h0401_0004;
      16'h0008: return 32'h0500_0100;
      16'h0009: return 32'h0600_0200;
      16'h000A: return 32'h0700_0300;
      16'h000B: return 32'h0800_0400;
      16'h000C: return 32'h8001_0004;
      16'h000D: return 32'h0000_0000;
      16'h000E: return 32'h0000_0000;
      16'h000F: return 32'h0000_0000;
      16'h0010: return 32'h0000_0000;
      default : return 32'h8001_0001;
    endcase
  endfunction

  // Functional correctness: 1-cycle registered lookup
  property p_lookup_correct;
    @(posedge clk) past_valid |-> (data_o == exp_data($past(addr_i)));
  endproperty
  assert property (p_lookup_correct)
    else $error("nkmd_progrom: data_o mismatch vs expected lookup of prior addr_i");

  // Default path must be taken when upper 16 bits are non-zero
  property p_highbits_force_default;
    @(posedge clk) past_valid && ($past(addr_i[31:16]) != 16'h0000)
      |-> (data_o == 32'h8001_0001);
  endproperty
  assert property (p_highbits_force_default)
    else $error("nkmd_progrom: nonzero upper addr must return default value");

  // No X/Z on observable interface after first cycle
  property p_no_xz;
    @(posedge clk) past_valid |-> (!$isunknown(addr_i) && !$isunknown(data_o));
  endproperty
  assert property (p_no_xz)
    else $error("nkmd_progrom: X/Z detected on addr_i or data_o");

  // Coverage: hit each table entry (addr[31:16]==0, low 16 from 0..16)
  genvar i;
  generate
    for (i = 0; i <= 16; i++) begin : C_ADDRS
      cover property (@(posedge clk)
        past_valid && $past(addr_i[31:16]) == 16'h0000 && $past(addr_i[15:0]) == i[15:0]);
    end
  endgenerate

  // Coverage: exercise default via (a) nonzero upper bits and (b) out-of-range low16 with zero upper
  cover property (@(posedge clk) past_valid && $past(addr_i[31:16]) != 16'h0000);
  cover property (@(posedge clk) past_valid && $past(addr_i[31:16]) == 16'h0000 && $past(addr_i[15:0]) > 16'h0010);

endmodule

// Bind into DUT
bind nkmd_progrom nkmd_progrom_sva svai(.clk(clk), .addr_i(addr_i), .data_o(data_o));