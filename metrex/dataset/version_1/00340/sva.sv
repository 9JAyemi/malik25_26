// SVA checker for vga_palette_regs_fml
// Bind example:
// bind vga_palette_regs_fml vga_palette_regs_fml_sva sva (.*);

module vga_palette_regs_fml_sva (
  input clk,
  input      [3:0] attr,
  input      [3:0] address,
  input            write,
  input      [7:0] write_data,
  input      [7:0] index,
  input      [7:0] read_data
);
  localparam int N = 16;

  // Minimal shadow model (tracks only what’s been written)
  logic [7:0] model_mem      [0:N-1];
  logic [7:0] model_mem_prev [0:N-1];
  logic [N-1:0] valid, valid_prev;

  initial begin
    valid      = '0;
    valid_prev = '0;
    foreach (model_mem[i]) begin
      model_mem[i]      = 'x;
      model_mem_prev[i] = 'x;
    end
  end

  always_ff @(posedge clk) begin
    for (int i = 0; i < N; i++) model_mem_prev[i] <= model_mem[i];
    valid_prev <= valid;
    if (write) begin
      model_mem[address] <= write_data;
      valid[address]     <= 1'b1;
    end
  end

  default clocking cb @(posedge clk); endclocking

  // Basic sanity on controls
  assert property ( !$isunknown({attr, address, write}) );
  assert property ( write |-> !$isunknown(write_data) );

  // Outputs must reflect previous-cycle memory contents (no write-through)
  assert property ( valid_prev[attr]    |-> index     == model_mem_prev[attr]    );
  assert property ( valid_prev[address] |-> read_data == model_mem_prev[address] );

  // When selected address equals written address, new data must be visible next cycle
  assert property ( write ##1 (attr    == $past(address)) |-> index     == $past(write_data) );
  assert property ( write ##1 (address == $past(address)) |-> read_data == $past(write_data) );

  // Outputs should not be X when data is known
  assert property ( valid_prev[attr]    |-> !$isunknown(index)     );
  assert property ( valid_prev[address] |-> !$isunknown(read_data) );

  // Coverage
  // - Exercise all addresses on write/read and attr path
  generate
    genvar i;
    for (i = 0; i < N; i++) begin : COV_ADDRS
      cover property ( write && address == i[3:0] );
      cover property ( address == i[3:0] && valid_prev[i] );
      cover property ( attr    == i[3:0] && valid_prev[i] );
    end
  endgenerate

  // - Same-cycle hazard (read same address as being written; must be old value)
  cover property ( write && (attr == address) );

  // - Next-cycle visibility of write on both ports
  cover property ( write ##1 (attr    == $past(address)  && index     == $past(write_data)) );
  cover property ( write ##1 (address == $past(address)  && read_data == $past(write_data)) );

  // - Extremes
  cover property ( write && address == 4'h0 && write_data == 8'h00 );
  cover property ( write && address == 4'hF && write_data == 8'hFF );

endmodule