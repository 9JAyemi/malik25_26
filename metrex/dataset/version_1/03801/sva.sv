// SVA checker for dual_port_ram
// BIND THIS: bind dual_port_ram dual_port_ram_sva i_dual_port_ram_sva (.*);

module dual_port_ram_sva (
  input logic         clock,
  input logic [31:0]  data_a,
  input logic         wren_a,
  input logic [4:0]   address_a,
  input logic [31:0]  data_b,
  input logic         wren_b,
  input logic [4:0]   address_b,
  input logic         rd_en_a,
  input logic         rd_en_b,
  input logic [31:0]  q_a,
  input logic [31:0]  q_b
);

  // Shadow model (matches DUT semantics: synchronous read of previous contents; write B overrides A on same addr)
  logic               past_v;
  logic [31:0]        ref_mem [0:31];
  logic [31:0]        valid_bits; // 1 per address when written at least once

  function automatic bit good_addr(input logic [4:0] a);
    return !$isunknown(a);
  endfunction

  // Update reference memory and valid-bits
  always_ff @(posedge clock) begin
    past_v <= 1'b1;
    if (wren_a && good_addr(address_a)) begin
      ref_mem[address_a] <= data_a;
      valid_bits[address_a] <= 1'b1;
    end
    if (wren_b && good_addr(address_b)) begin
      ref_mem[address_b] <= data_b;     // overrides A if same address
      valid_bits[address_b] <= 1'b1;
    end
  end

  // Helper conditions
  wire va = good_addr(address_a) && valid_bits[address_a];
  wire vb = good_addr(address_b) && valid_bits[address_b];

  // Read data correctness (synchronous read of previous contents)
  // When rd_en asserted and address is known and previously initialized, q matches previous memory contents
  assert property (@(posedge clock) past_v && rd_en_a && va |-> q_a == $past(ref_mem[address_a]))
    else $error("q_a mismatch with shadow memory");
  assert property (@(posedge clock) past_v && rd_en_b && vb |-> q_b == $past(ref_mem[address_b]))
    else $error("q_b mismatch with shadow memory");

  // Read-during-write behavior (same-cycle write does not bypass; still returns old data)
  // Same-port RAW
  assert property (@(posedge clock) past_v && rd_en_a && wren_a && good_addr(address_a) |-> q_a == $past(ref_mem[address_a]))
    else $error("q_a RAW (same-port) should return old data");
  assert property (@(posedge clock) past_v && rd_en_b && wren_b && good_addr(address_b) |-> q_b == $past(ref_mem[address_b]))
    else $error("q_b RAW (same-port) should return old data");
  // Cross-port RAW
  assert property (@(posedge clock) past_v && rd_en_a && wren_b && good_addr(address_a) && good_addr(address_b) && (address_a==address_b)
                   |-> q_a == $past(ref_mem[address_a]))
    else $error("q_a RAW (cross-port) should return old data");
  assert property (@(posedge clock) past_v && rd_en_b && wren_a && good_addr(address_a) && good_addr(address_b) && (address_a==address_b)
                   |-> q_b == $past(ref_mem[address_b]))
    else $error("q_b RAW (cross-port) should return old data");

  // Output hold when rd_en deasserted
  assert property (@(posedge clock) past_v && !rd_en_a |-> q_a == $past(q_a))
    else $error("q_a changed without rd_en_a");
  assert property (@(posedge clock) past_v && !rd_en_b |-> q_b == $past(q_b))
    else $error("q_b changed without rd_en_b");

  // Collision semantics: if both write same addr in a cycle, next read of that addr returns data_b
  // (Checked via shadow model; this assertion fires on the next-cycle read)
  assert property (@(posedge clock)
                   past_v && $past(wren_a && wren_b && good_addr(address_a) && good_addr(address_b) && (address_a==address_b)) &&
                   rd_en_a && good_addr(address_a) && (address_a == $past(address_a))
                   |-> q_a == $past(data_b))
    else $error("Collision A: next read did not reflect port B's data");
  assert property (@(posedge clock)
                   past_v && $past(wren_a && wren_b && good_addr(address_a) && good_addr(address_b) && (address_a==address_b)) &&
                   rd_en_b && good_addr(address_b) && (address_b == $past(address_b))
                   |-> q_b == $past(data_b))
    else $error("Collision B: next read did not reflect port B's data");

  // Basic cover: exercise ops and hazards
  cover property (@(posedge clock) wren_a);
  cover property (@(posedge clock) wren_b);
  cover property (@(posedge clock) rd_en_a);
  cover property (@(posedge clock) rd_en_b);
  cover property (@(posedge clock) wren_a && wren_b && good_addr(address_a) && (address_a==address_b));                         // write-write collision
  cover property (@(posedge clock) rd_en_a && rd_en_b && good_addr(address_a) && good_addr(address_b) && (address_a==address_b)); // read same addr both ports
  cover property (@(posedge clock) wren_a && rd_en_a);                                                                            // same-port RAW A
  cover property (@(posedge clock) wren_b && rd_en_b);                                                                            // same-port RAW B
  cover property (@(posedge clock) wren_a && rd_en_b && good_addr(address_a) && good_addr(address_b) && (address_a==address_b));  // cross RAW A->B
  cover property (@(posedge clock) wren_b && rd_en_a && good_addr(address_a) && good_addr(address_b) && (address_a==address_b));  // cross RAW B->A

  // Address coverage (reads and writes hit all locations)
  genvar i;
  generate
    for (i=0; i<32; i++) begin : COV_ADDRS
      cover property (@(posedge clock) wren_a && address_a == i[4:0]);
      cover property (@(posedge clock) wren_b && address_b == i[4:0]);
      cover property (@(posedge clock) rd_en_a && address_a == i[4:0]);
      cover property (@(posedge clock) rd_en_b && address_b == i[4:0]);
    end
  endgenerate

endmodule