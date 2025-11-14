// SVA for module memory
module memory_sva #(
  parameter bits  = 32,
  parameter words = 1024
)(
  input logic                 clk,
  input logic [9:0]           addr,
  input logic [bits-1:0]      data_in,
  input logic [bits-1:0]      mem
);

  localparam int ADDR_W   = $bits(addr);
  localparam int MAX_ADDR = (1<<ADDR_W) - 1;

  default clocking cb @(posedge clk); endclocking

  // Guard $past on first cycle
  logic past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge clk) past_valid <= 1'b1;
  default disable iff (!past_valid);

  // Core behavior: valid addr => mem updates to data_in the same cycle
  a_update_on_valid: assert property (addr < words |=> mem == data_in);

  // Out-of-range addr => mem holds previous value
  a_hold_on_invalid: assert property (addr >= words |=> mem == $past(mem));

  // Any mem change must be due to a valid addr and must reflect data_in
  a_change_only_when_valid: assert property ((mem != $past(mem)) |=> (addr < words) && (mem == data_in));

  // Sanity: control/data not X when used
  a_no_x_addr:   assert property (!$isunknown(addr));
  a_no_x_data_wen: assert property ((addr < words) |-> !$isunknown(data_in));

  // Coverage
  c_write_any:    cover property (addr < words && mem == data_in);
  generate
    if (words > 0 && (words-1) <= MAX_ADDR) begin : gen_cov_hi
      c_write_high: cover property (addr == (words-1) && mem == data_in);
    end
    if (0 < words) begin : gen_cov_lo
      c_write_low:  cover property (addr == 0 && mem == data_in);
    end
    if (words <= MAX_ADDR) begin : gen_cov_inv
      c_invalid_seen: cover property (addr >= words ##1 mem == $past(mem));
    end
  endgenerate

endmodule

// Bind into the DUT
bind memory memory_sva #(.bits(bits), .words(words)) u_memory_sva (.*);