// SVA checker for memory; bind to DUT
module memory_sva #(
  parameter int ADDR_W = 6,
  parameter int DATA_W = 32,
  parameter int DEPTH  = (1<<ADDR_W)
)(
  input  logic                  clk,
  input  logic                  we,
  input  logic [ADDR_W-1:0]     a,
  input  logic [DATA_W-1:0]     d,
  input  logic [DATA_W-1:0]     spo,
  input  logic [DATA_W-1:0]     mem_out
);

  // Shadow model
  logic [DATA_W-1:0] ref_mem [DEPTH];
  bit   [DEPTH-1:0]  written;

  // Update model on valid writes
  always_ff @(posedge clk) begin
    if (we && !$isunknown(a)) begin
      ref_mem[a]  <= d;
      written[a]  <= 1'b1;
    end
  end

  // Structural equivalence
  assert_spo_taps_memout:
    assert property (@(posedge clk) spo === mem_out);

  // No X/Z on critical controls at write
  assert_no_x_on_write:
    assert property (@(posedge clk) we |-> (!$isunknown(a) && !$isunknown(d)));

  // Once initialized for this address, read must match model
  assert_read_matches_model:
    assert property (@(posedge clk) (!$isunknown(a) && written[a]) |-> (spo === ref_mem[a]));

  // Write -> next-cycle readback if address stable
  assert_wr_rdback_1cyc:
    assert property (@(posedge clk) we && $stable(a) |=> (spo === $past(d)));

  // No write and address stable -> output stable
  assert_stable_when_idle:
    assert property (@(posedge clk) !we && $stable(a) |=> $stable(spo));

  // After initialization of this address, spo must not be X/Z
  assert_no_x_after_init:
    assert property (@(posedge clk) (!$isunknown(a) && written[a]) |-> !$isunknown(spo));

  // Coverage
  cover_any_write:
    cover property (@(posedge clk) we);

  cover_min_addr_write:
    cover property (@(posedge clk) we && (a == '0));

  cover_max_addr_write:
    cover property (@(posedge clk) we && (a == DEPTH-1));

  cover_wr_then_rdback_same_addr:
    cover property (@(posedge clk) we && $stable(a) ##1 (spo === $past(d)));

  cover_b2b_writes_same_addr:
    cover property (@(posedge clk) we ##1 (we && a == $past(a)));

  cover_b2b_writes_diff_addr:
    cover property (@(posedge clk) we ##1 (we && a != $past(a)));

endmodule

// Bind into DUT (connect internal mem_out)
bind memory memory_sva #(.ADDR_W(6), .DATA_W(32), .DEPTH(64)) u_memory_sva (
  .clk     (clk),
  .we      (we),
  .a       (a),
  .d       (d),
  .spo     (spo),
  .mem_out (mem_out)
);