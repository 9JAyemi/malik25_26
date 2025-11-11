// SVA for memory: concise, high-quality checks and coverage
// Bindable checker with a tiny scoreboard and key properties

module memory_sva #(
  parameter int ADDR_W = 10,
  parameter int DATA_W = 12,
  parameter int DEPTH  = 1 << ADDR_W
)(
  input  logic                   clock,
  input  logic [ADDR_W-1:0]      address,
  input  logic [DATA_W-1:0]      data_in,
  input  logic                   write_en,
  input  logic [DATA_W-1:0]      data_out
);

  // Simple reference model of the memory contents + valid mask
  logic [DATA_W-1:0] ref_mem [0:DEPTH-1];
  bit                ref_val [0:DEPTH-1];

  initial begin
    for (int i = 0; i < DEPTH; i++) ref_val[i] = 1'b0;
  end

  // Basic input X/Z checks
  assert property (@(posedge clock) !$isunknown(write_en))
    else $error("memory_sva: write_en is X/Z");
  assert property (@(posedge clock) write_en |-> (!$isunknown(address) && !$isunknown(data_in)))
    else $error("memory_sva: write with X/Z address or data_in");

  // Registered read must return the previously stored content (no write-through)
  // Compare using pre-update ref_mem; then update scoreboard for next cycle
  always_ff @(posedge clock) begin
    if (!$isunknown(address) && ref_val[address]) begin
      assert (data_out === ref_mem[address])
        else $error("memory_sva: data_out mismatch at addr=%0d exp=%0h got=%0h",
                    address, ref_mem[address], data_out);
    end
    if (write_en && !$isunknown(address) && !$isunknown(data_in)) begin
      ref_mem[address] <= data_in;
      ref_val[address] <= 1'b1;
    end
  end

  // 1-cycle RAW to same address must return the newly written data
  property p_raw_1cycle_same_addr;
    @(posedge clock)
      write_en |-> ##1 ((address != $past(address)) || (data_out == $past(data_in)));
  endproperty
  assert property (p_raw_1cycle_same_addr)
    else $error("memory_sva: 1-cycle RAW (same addr) failed");

  // data_out must be stable between rising edges (registered output)
  assert property (@(negedge clock) $stable(data_out))
    else $error("memory_sva: data_out changed outside posedge");

  // Functional coverage
  cover property (@(posedge clock) write_en); // any write
  cover property (@(posedge clock) !write_en); // pure read cycle
  cover property (@(posedge clock) write_en ##1 (address == $past(address) && data_out == $past(data_in))); // RAW same addr
  cover property (@(posedge clock) write_en && $past(write_en) && (address == $past(address)) && (data_in != $past(data_in))); // back-to-back writes to same addr with new data
  cover property (@(posedge clock) address == '0); // lowest address accessed
  cover property (@(posedge clock) address == (DEPTH-1)); // highest address accessed

endmodule

// Bind into the DUT
bind memory memory_sva #(.ADDR_W(10), .DATA_W(12)) memory_sva_i (
  .clock   (clock),
  .address (address),
  .data_in (data_in),
  .write_en(write_en),
  .data_out(data_out)
);