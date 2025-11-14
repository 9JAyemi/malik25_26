// SVA for ECC_memory_block
// Concise, high-quality checks with a small predictor using only DUT I/Os.
// Bind this file without modifying the DUT.

`ifndef ECC_MEMORY_BLOCK_SVA
`define ECC_MEMORY_BLOCK_SVA

module ECC_memory_block_sva #(
  parameter int data_width = 8,
  parameter int ecc_width  = 4,
  parameter int addr_width = 8
) (
  input  logic                     clk,
  input  logic                     rst,
  input  logic [data_width-1:0]    data_in,
  input  logic [addr_width-1:0]    addr,
  input  logic                     we,
  output logic [data_width-1:0]    data_out,
  output logic [ecc_width-1:0]     ecc
);

  // Re-implement DUT helper functions for checking
  function automatic logic [ecc_width-1:0]
    hamming_code_sva (logic [data_width-1:0] data);
    logic [ecc_width-1:0] e; int i;
    begin
      e = '0;
      for (i = 0; i < ecc_width; i++) begin
        e[i] = data[i] ^ data[i+1] ^ data[i+3];
      end
      e[ecc_width-1] = data[0] ^ data[1] ^ data[2];
      return e;
    end
  endfunction

  function automatic logic [data_width-1:0]
    error_correction_sva (logic [data_width-1:0] data, logic [ecc_width-1:0] e);
    logic [data_width-1:0] c; int i;
    begin
      for (i = 0; i < data_width; i++) begin
        c[i] = data[i] ^ (e[0] ^ e[1] ^ e[3]);
      end
      c[data_width-1] = data[data_width-1] ^ (e[0] ^ e[1] ^ e[2]);
      return c;
    end
  endfunction

  // Lightweight predictor (from visible I/Os; DUT memory is not observable)
  typedef logic [addr_width-1:0] addr_t;
  typedef logic [data_width-1:0] data_t;
  typedef logic [ecc_width-1:0]  ecc_t;

  data_t ref_mem [addr_t];
  bit    has_data [addr_t];
  ecc_t  exp_ecc_reg;

  // Predictor update: mirrors DUT behavior observable at ports
  always_ff @(posedge clk) begin
    if (rst) begin
      exp_ecc_reg <= '0;     // DUT clears ecc_reg on reset
      // ref_mem/has_data unchanged: DUT memory is not reset
    end else if (we) begin
      ref_mem[addr] <= data_in;
      has_data[addr] <= 1'b1;
      exp_ecc_reg <= hamming_code_sva(data_in);
    end
  end

  // Assertions
  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Reset effect on ecc port (mirrors ecc_reg)
  assert property (rst |=> ecc == '0);

  // ECC updates on write with proper code; stays stable on read
  assert property (we  |=> ecc == hamming_code_sva($past(data_in)));
  assert property (!we |=> $stable(ecc));
  // ECC port always equals predictor
  assert property (ecc == exp_ecc_reg);

  // Read behavior: next cycle data_out equals predicted corrected/pass-through data,
  // but only for addresses we have written (unknown DUT memory otherwise)
  property p_read_returns_expected;
    addr_t a; data_t d; ecc_t e;
    (!we && has_data[addr], a = addr, d = ref_mem[addr], e = exp_ecc_reg)
      |=> data_out == ((hamming_code_sva(d) != e) ? error_correction_sva(d, e) : d);
  endproperty
  assert property (p_read_returns_expected);

  // Sanity: outputs are known when we can predict them
  assert property ((!we && has_data[addr]) |=> !$isunknown(data_out));
  assert property (!$isunknown(ecc));

  // Coverage
  cover property (we);                                        // write seen
  cover property (!we && has_data[addr]);                     // readable address seen
  cover property ((!we && has_data[addr] &&
                   (hamming_code_sva(ref_mem[addr]) == exp_ecc_reg))); // no-correction path
  cover property ((!we && has_data[addr] &&
                   (hamming_code_sva(ref_mem[addr]) != exp_ecc_reg))); // correction path
  cover property (we ##1 (!we && has_data[$past(addr)]));     // write -> read
  cover property ((!we && has_data[addr]) ##1 we);            // read -> write

endmodule

// Bind the checker to every ECC_memory_block instance
bind ECC_memory_block ECC_memory_block_sva #(
  .data_width(data_width),
  .ecc_width (ecc_width),
  .addr_width(addr_width)
) u_ecc_memory_block_sva (.*);

`endif